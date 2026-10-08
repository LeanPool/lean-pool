/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push


/-!
# Phillips' lemma (Lemmas 2.2 and 2.3)

**Lemma 2.2** (`lem:Phillips`). Let `(μ_n)` be a sequence in `(ℓ^∞(ℕ))*` such that
`μ_n(a) → 0` for every `a ∈ ℓ^∞(ℕ)`. Then `Σ_k |μ_n(e_k)| → 0`; in particular
`μ_n(e_n) → 0`.

**Lemma 2.3** (`lem:cor-Phillips`). Let `S ∈ 𝓛(ℓ^∞(ℕ), X)` and `t_n ≥ 0` with `t_n → 0`.
Then `‖(T_{t_n} - Id) S e_n‖ → 0`.

## Main declarations

* `Phillips.full` : **Lemma 2.2** (summability of each `Σ_k |μ_n(e_k)|`, convergence of the
  sums to `0`, and `μ_n(e_n) → 0`); `Phillips.tsum_abs_tendsto_zero` is the real case
  written with absolute values.
* `Phillips.uniform` : **Lemma 2.3**. Only strong right-continuity of `T` at `0` is used;
  the semigroup law and completeness are not needed.

`Linfty 𝕜` is the space of bounded sequences with values in `𝕜 = ℝ` or `ℂ`, represented as
bounded continuous functions on the discrete space `ℕ`; `e k` is the `k`-th canonical
vector. The paper quotes Lemma 2.2 from [Phillips 1940]; here it is proved.

## Proof of Lemma 2.2

1. Diagonal statement, `diagonal_tendsto_zero`: `μ_n(e_n) → 0`. An infinite set of indices
   is thinned so that a given functional is small on all its subsets (`small_on_subsets`);
   a recursive selection then produces a set `A` for which `μ_n(1_A)` cannot tend to zero
   (`diagonal_of_indicator_tendsto`). Only finite sums are used.
2. For a single functional, `Σ_{k ∈ s} |φ(e_k)| ≤ ‖φ‖` for every finite `s`, by testing `φ`
   on `Σ_{k ∈ s} λ_k e_k` with phases `|λ_k| ≤ 1` (`sum_norm_eval_le`); hence the series
   converge (`summable_norm_eval`).
3. Disjoint finite blocks `B_j` with coefficients of modulus `≤ 1` are encoded by one bounded
   operator `S : ℓ^∞ → ℓ^∞` with `S e_j` supported in `B_j`, defined coordinatewise
   (`exists_block_operator`).
4. Gliding hump (`finite_sum_eventually_small`): if finite sums were not eventually uniformly
   small, Steps 2–3 would produce functionals `ν_j = μ_{r_j} ∘ S` contradicting Step 1.
   This gives `Σ_k |μ_n(e_k)| → 0` (`tsum_norm_tendsto_zero`).

Lemma 2.3 (`uniform`) applies the diagonal statement to `μ_n = x_n^* ∘ (T_{t_n} - Id) ∘ S`,
with norming functionals `x_n^*` given by Hahn–Banach (`norm_diagonal_tendsto_zero`).
-/

namespace AbstractLinearControl

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology


namespace Phillips

attribute [local instance] Classical.propDecidable

/-- Bounded scalar sequences, with the supremum norm. -/
abbrev Linfty (𝕜 : Type*) [RCLike 𝕜] := BoundedContinuousFunction ℕ 𝕜

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The characteristic sequence of a set of natural numbers. -/
def chi (S : Set ℕ) : Linfty 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => if k ∈ S then (1 : 𝕜) else 0) 1
    (by
      intro k
      by_cases hk : k ∈ S <;> simp [hk])

@[simp] theorem chi_apply (S : Set ℕ) (k : ℕ) :
    chi (𝕜 := 𝕜) S k = if k ∈ S then 1 else 0 := rfl

/-- The `k`th canonical vector of `ℓ∞`. -/
def e (k : ℕ) : Linfty 𝕜 := chi {k}

@[simp] theorem e_apply (k j : ℕ) :
    e (𝕜 := 𝕜) k j = if j = k then 1 else 0 := by
  simp [e]
/-! ## Step 1: the diagonal statement `μ_n(e_n) → 0` -/

/-- An infinite set can be thinned so that a given functional is small on
all characteristic sequences supported in the remaining set. -/
private theorem small_on_subsets
    (φ : Linfty 𝕜 →L[𝕜] 𝕜) (S : Set ℕ) (hS : S.Infinite)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧
      ∀ B : Set ℕ, B ⊆ T → ‖φ (chi B)‖ ≤ δ := by
  classical
  -- Partition an infinite subset of S into infinitely many infinite sets.
  let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hS
  let g : ℕ × ℕ → ℕ := fun p => (emb (Nat.pair p.1 p.2)).val
  have hg : Function.Injective g := by
    intro p q hpq
    have hpq' : Nat.pair p.1 p.2 = Nat.pair q.1 q.2 :=
      emb.injective (Subtype.ext hpq)
    exact Nat.pairEquiv.injective hpq'
  let A : ℕ → Set ℕ := fun i => Set.range (fun j => g (i, j))
  have hAinf (i : ℕ) : (A i).Infinite := by
    apply Set.infinite_range_of_injective
    intro j k hjk
    exact congrArg Prod.snd (hg hjk)
  have hAS (i : ℕ) : A i ⊆ S := by
    rintro x ⟨j, rfl⟩
    exact (emb (Nat.pair i j)).property
  by_contra h
  have hbad : ∀ i : ℕ, ∃ B : Set ℕ, B ⊆ A i ∧ δ < ‖φ (chi B)‖ := by
    intro i
    by_contra hi
    apply h
    refine ⟨A i, hAS i, hAinf i, ?_⟩
    intro B hBA
    by_contra hle
    exact hi ⟨B, hBA, lt_of_not_ge hle⟩
  choose B hBA hBδ using hbad
  have hdisj {i j x : ℕ} (hi : x ∈ B i) (hj : x ∈ B j) : i = j := by
    obtain ⟨a, ha⟩ := hBA i hi
    obtain ⟨b, hb⟩ := hBA j hj
    exact congrArg Prod.fst (hg (ha.trans hb.symm))
  have hz (i : ℕ) : φ (chi (B i)) ≠ 0 :=
    norm_pos_iff.mp (hδ.trans (hBδ i))
  -- Normalize each witness so that its image under φ is exactly 1.
  let v : ℕ → Linfty 𝕜 := fun i => (φ (chi (B i)))⁻¹ • chi (B i)
  have hv (i : ℕ) : φ (v i) = 1 := by
    simp [v, map_smul, smul_eq_mul, hz i]
  have hcoef (i : ℕ) : ‖(φ (chi (B i)))⁻¹‖ ≤ δ⁻¹ := by
    simpa only [norm_inv, one_div] using
      (one_div_le_one_div_of_le hδ (le_of_lt (hBδ i)))
  -- Disjoint supports give a norm bound independent of the number of terms.
  have hsum (s : Finset ℕ) : ‖∑ i ∈ s, v i‖ ≤ δ⁻¹ := by
    apply (BoundedContinuousFunction.norm_le (show 0 ≤ δ⁻¹ by positivity)).2
    intro x
    rw [BoundedContinuousFunction.sum_apply]
    by_cases hx : ∃ i ∈ s, x ∈ B i
    · obtain ⟨i, hi, hxi⟩ := hx
      have heq : (∑ j ∈ s, (v j) x) = (v i) x := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          have hxj : x ∉ B j := fun hxj => hji (hdisj hxj hxi)
          simp [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxj]
        · intro hnot
          exact (hnot hi).elim
      rw [heq]
      simpa [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxi] using hcoef i
    · have hzero : ∀ i ∈ s, (v i) x = 0 := by
        intro i hi
        have hxi : x ∉ B i := fun hxi => hx ⟨i, hi, hxi⟩
        simp [v, BoundedContinuousFunction.smul_apply, smul_eq_mul, hxi]
      rw [Finset.sum_eq_zero hzero, norm_zero]
      positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (‖φ‖ * δ⁻¹)
  have hval : φ (∑ i ∈ Finset.range N, v i) = (N : 𝕜) := by
    simp [map_sum, hv]
  have hup : ‖φ (∑ i ∈ Finset.range N, v i)‖ ≤ ‖φ‖ * δ⁻¹ :=
    (φ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hsum _) (norm_nonneg φ))
  rw [hval, RCLike.norm_natCast] at hup
  exact (not_le_of_gt hN) hup
/-- It is enough to assume convergence on characteristic sequences. -/
theorem diagonal_of_indicator_tendsto
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ S : Set ℕ, Tendsto (fun n => μ n (chi S)) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (e n)) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ε ≤ ‖μ n (e n)‖ := by
    push Not at hnot
    simpa only [dist_zero_right] using hnot
  let D : Set ℕ := {n | ε ≤ ‖μ n (e n)‖}
  have hD : D.Infinite := by
    intro hfin
    obtain ⟨N, hN⟩ := Set.exists_upper_bound_image D (fun n : ℕ => n) hfin
    obtain ⟨n, hn, hbn⟩ := hbad (N + 1)
    have hle : n ≤ N := hN n hbn
    omega
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  -- A reservoir is an infinite subset of the bad indices.
  let X := {S : Set ℕ // S.Infinite ∧ S ⊆ D}
  have hstep : ∀ (F : Set ℕ) (S : X), ∃ (n : ℕ) (T : X),
      n ∈ S.val ∧
      ‖μ n (chi F)‖ < δ ∧
      T.val ⊆ S.val ∧
      (∀ m ∈ T.val, n < m) ∧
      (∀ B : Set ℕ, B ⊆ T.val → ‖μ n (chi B)‖ ≤ δ) := by
    intro F S
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hμ F)) δ hδ
    obtain ⟨n, hnS, hnN⟩ :=
      S.property.1.exists_notMem_finite (Set.finite_lt_nat N)
    have hNn : N ≤ n := by
      simpa only [Set.mem_ofPred_eq, not_lt] using hnN
    have hnsmall : ‖μ n (chi F)‖ < δ := by
      simpa only [dist_zero_right] using hN n hNn
    have hSinfinite : (S.val \ {m : ℕ | m ≤ n}).Infinite :=
      S.property.1.sdiff (Set.finite_le_nat n)
    obtain ⟨T, hTS, hTinf, hTsmall⟩ :=
      small_on_subsets (μ n) (S.val \ {m : ℕ | m ≤ n}) hSinfinite δ hδ
    have hTsub : T ⊆ S.val := fun m hm => (hTS hm).1
    have hTD : T ⊆ D := fun m hm => S.property.2 (hTsub hm)
    refine ⟨n, ⟨T, hTinf, hTD⟩, hnS, hnsmall, hTsub, ?_, hTsmall⟩
    intro m hm
    exact lt_of_not_ge (hTS hm).2
  choose pick tail hpick hhead hsub hgt hsmall using hstep
  -- State = (already selected indices, current infinite reservoir).
  let state : ℕ → Set ℕ × X :=
    Nat.rec (∅, ⟨D, hD, fun _ h => h⟩)
      (fun _ p => (insert (pick p.1 p.2) p.1, tail p.1 p.2))
  let n : ℕ → ℕ := fun i => pick (state i).1 (state i).2
  let F : ℕ → Set ℕ := fun i => (state i).1
  let R : ℕ → Set ℕ := fun i => ((state i).2).val
  have hF0 : F 0 = ∅ := rfl
  have hFs (i : ℕ) : F (i + 1) = insert (n i) (F i) := rfl
  have hnmem (i : ℕ) : n i ∈ R i := hpick (state i).1 (state i).2
  have hRsub (i : ℕ) : R (i + 1) ⊆ R i := hsub (state i).1 (state i).2
  have hRgt (i : ℕ) : ∀ m ∈ R (i + 1), n i < m :=
    hgt (state i).1 (state i).2
  have hhead' (i : ℕ) : ‖μ (n i) (chi (F i))‖ < δ :=
    hhead (state i).1 (state i).2
  have hsmall' (i : ℕ) :
      ∀ B : Set ℕ, B ⊆ R (i + 1) → ‖μ (n i) (chi B)‖ ≤ δ :=
    hsmall (state i).1 (state i).2
  have hnD (i : ℕ) : ε ≤ ‖μ (n i) (e (n i))‖ :=
    (state i).2.property.2 (hnmem i)
  have hnstep (i : ℕ) : n i < n (i + 1) := hRgt i _ (hnmem (i + 1))
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ hnstep
  have hRanti : Antitone R := antitone_nat_of_succ_le hRsub
  have hin : ∀ i : ℕ, i ≤ n i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
        have hi := hnstep i
        omega
  have hFmem : ∀ (i x : ℕ), x ∈ F i ↔ ∃ j < i, n j = x := by
    intro i
    induction i with
    | zero =>
        intro x
        simp [hF0]
    | succ i ih =>
        intro x
        rw [hFs, Set.mem_insert_iff, ih]
        constructor
        · rintro (hxi | ⟨j, hj, hjx⟩)
          · exact ⟨i, Nat.lt_succ_self i, hxi.symm⟩
          · exact ⟨j, by omega, hjx⟩
        · rintro ⟨j, hj, hjx⟩
          by_cases hji : j = i
          · left
            simpa [hji] using hjx.symm
          · right
            exact ⟨j, by omega, hjx⟩
  let A : Set ℕ := Set.range n
  let B : ℕ → Set ℕ := fun i => {x | ∃ j, i < j ∧ n j = x}
  have hBsub (i : ℕ) : B i ⊆ R (i + 1) := by
    rintro x ⟨j, hij, rfl⟩
    exact hRanti (Nat.succ_le_of_lt hij) (hnmem j)
  have hsplit (i : ℕ) :
      chi (𝕜 := 𝕜) A = chi (F i) + e (n i) + chi (B i) := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [BoundedContinuousFunction.add_apply, chi_apply, e_apply]
    by_cases hx : x ∈ A
    · obtain ⟨j, rfl⟩ := hx
      have hA : n j ∈ A := ⟨j, rfl⟩
      have hF : n j ∈ F i ↔ j < i := by
        rw [hFmem]
        constructor
        · rintro ⟨k, hk, hkj⟩
          exact hnmono.injective hkj ▸ hk
        · intro hji
          exact ⟨j, hji, rfl⟩
      have hB : n j ∈ B i ↔ i < j := by
        change (∃ k, i < k ∧ n k = n j) ↔ i < j
        constructor
        · rintro ⟨k, hk, hkj⟩
          exact hnmono.injective hkj ▸ hk
        · intro hij
          exact ⟨j, hij, rfl⟩
      have heq : n j = n i ↔ j = i :=
        ⟨fun h => hnmono.injective h, fun h => congrArg n h⟩
      rcases lt_trichotomy j i with hji | hji | hij
      · simp [hA, hF, hB, heq, hji, ne_of_lt hji, not_lt_of_ge (le_of_lt hji)]
      · subst j
        simp [hA, hF, hB]
      · simp [hA, hF, hB, heq, hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
    · have hxF : x ∉ F i := by
        intro hxF
        obtain ⟨j, hj, hjx⟩ := (hFmem i x).1 hxF
        exact hx ⟨j, hjx⟩
      have hxB : x ∉ B i := by
        rintro ⟨j, hj, hjx⟩
        exact hx ⟨j, hjx⟩
      have hxn : x ≠ n i := by
        intro hxn
        exact hx ⟨i, hxn.symm⟩
      simp [hx, hxF, hxB, hxn]
  -- The characteristic sequence of all selected indices contradicts hμ.
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hμ A)) δ hδ
  have hA_small : ‖μ (n N) (chi A)‖ < δ := by
    simpa only [dist_zero_right] using hN (n N) (hin N)
  have hF_small := hhead' N
  have hB_small := hsmall' N (B N) (hBsub N)
  have hidentity : μ (n N) (chi A) =
      μ (n N) (chi (F N)) + μ (n N) (e (n N)) + μ (n N) (chi (B N)) := by
    rw [hsplit N, map_add, map_add]
  have hdiag : μ (n N) (e (n N)) =
      μ (n N) (chi A) - μ (n N) (chi (F N)) - μ (n N) (chi (B N)) := by
    rw [hidentity]
    abel
  have hnorm : ‖μ (n N) (e (n N))‖ ≤
      ‖μ (n N) (chi A)‖ + ‖μ (n N) (chi (F N))‖ +
        ‖μ (n N) (chi (B N))‖ := by
    rw [hdiag]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hlarge := hnD N
  dsimp [δ] at hA_small hF_small hB_small
  linarith only [hε, hA_small, hF_small, hB_small, hnorm, hlarge]
/-- Step 1 (diagonal statement): if `μ_n(a) → 0` for every `a ∈ ℓ^∞`, then
`μ_n(e_n) → 0`. This is the "in particular" part of Lemma 2.2, proved first; the full
lemma (`Phillips.full`) is deduced from it. -/
theorem diagonal_tendsto_zero
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => μ n a) atTop (𝓝 0)) :
    Tendsto (fun n => μ n (e n)) atTop (𝓝 0) :=
  diagonal_of_indicator_tendsto μ (fun S => hμ (chi S))

end Phillips

namespace Phillips

open Filter
open scoped BigOperators Topology

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Step 2: finite sums `Σ_{k ∈ s} |φ(e_k)| ≤ ‖φ‖` -/

/-- Multiplying `z` by this scalar gives the nonnegative real `‖z‖`.
The coefficient is zero when `z = 0`. -/
private noncomputable def phase (z : 𝕜) : 𝕜 := (‖z‖ : 𝕜) / z

private theorem phase_mul (z : 𝕜) : phase z * z = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · exact div_mul_cancel₀ _ hz
private theorem norm_phase_le (z : 𝕜) : ‖phase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · have hn : ‖z‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hz)
    simpa only [phase, norm_div,
      RCLike.norm_of_nonneg (norm_nonneg z), div_self hn] using
      (le_refl (1 : ℝ))
/-- A finite linear combination of the canonical vectors. -/
private noncomputable def finiteVector (s : Finset ℕ) (c : ℕ → 𝕜) : Linfty 𝕜 :=
  ∑ k ∈ s, c k • e k

private theorem finiteVector_apply (s : Finset ℕ) (c : ℕ → 𝕜) (k : ℕ) :
    finiteVector s c k = if k ∈ s then c k else 0 := by
  classical
  simp only [finiteVector, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, e_apply, smul_eq_mul]
  by_cases hk : k ∈ s
  · rw [ite_eq_left hk]
    calc
      (∑ j ∈ s, c j * (if k = j then 1 else 0)) =
          c k * (if k = k then 1 else 0) := by
        apply Finset.sum_eq_single k
        · intro j hj hjk
          simp [Ne.symm hjk]
        · intro hnot
          exact (hnot hk).elim
      _ = c k := by simp
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hkj : k ≠ j := by
      intro h
      exact hk (h.symm ▸ hj)
    simp [hkj]
private theorem norm_finiteVector_le (s : Finset ℕ) (c : ℕ → 𝕜)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) :
    ‖finiteVector s c‖ ≤ 1 := by
  classical
  apply (BoundedContinuousFunction.norm_le (by positivity : (0 : ℝ) ≤ 1)).2
  intro k
  rw [finiteVector_apply]
  by_cases hk : k ∈ s
  · simpa only [ite_eq_left hk] using hc k
  · simp [hk]
private theorem norm_eval_finiteVector
    (φ : Linfty 𝕜 →L[𝕜] 𝕜) (s : Finset ℕ) :
    ‖φ (finiteVector s (fun k => phase (φ (e k))))‖ =
      ∑ k ∈ s, ‖φ (e k)‖ := by
  have heval : φ (finiteVector s (fun k => phase (φ (e k)))) =
      ((∑ k ∈ s, ‖φ (e k)‖ : ℝ) : 𝕜) := by
    simp only [finiteVector, map_sum, map_smul, smul_eq_mul, phase_mul]
  rw [heval]
  exact RCLike.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
/-- Every finite sum of the absolute values of the atomic coefficients is
bounded by the norm of the functional. -/
theorem sum_norm_eval_le (φ : Linfty 𝕜 →L[𝕜] 𝕜) (s : Finset ℕ) :
    (∑ k ∈ s, ‖φ (e k)‖) ≤ ‖φ‖ := by
  calc
    (∑ k ∈ s, ‖φ (e k)‖) =
        ‖φ (finiteVector s (fun k => phase (φ (e k))))‖ :=
      (norm_eval_finiteVector φ s).symm
    _ ≤ ‖φ‖ * ‖finiteVector s (fun k => phase (φ (e k)))‖ :=
      φ.le_opNorm _
    _ ≤ ‖φ‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_finiteVector_le s _ (fun k => norm_phase_le (φ (e k))))
        (norm_nonneg φ)
    _ = ‖φ‖ := mul_one _
/-- The atomic coefficients of any bounded functional on `ℓ∞` are in `ℓ¹`.
This requires no convergence hypothesis on a sequence of functionals. -/
theorem summable_norm_eval (φ : Linfty 𝕜 →L[𝕜] 𝕜) :
    Summable (fun k : ℕ => ‖φ (e k)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (sum_norm_eval_le φ)

/-- The `ℓ¹` norm of the atomic coefficients is at most the operator norm. -/
theorem tsum_norm_eval_le (φ : Linfty 𝕜 →L[𝕜] 𝕜) :
    (∑' k : ℕ, ‖φ (e k)‖) ≤ ‖φ‖ :=
  Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (sum_norm_eval_le φ)

/-! ## Step 3: disjoint finite blocks, encoded by one bounded operator `ℓ^∞ → ℓ^∞` -/

/-- Disjoint finite blocks with coefficients of norm at most one can be
encoded as the images of the canonical vectors under one bounded operator.
The operator is defined coordinatewise, not by a norm-convergent series. -/
private theorem exists_block_operator
    (s : ℕ → Finset ℕ)
    (hs : ∀ i j k : ℕ, k ∈ s i → k ∈ s j → i = j)
    (c : ℕ → ℕ → 𝕜)
    (hc : ∀ i k : ℕ, ‖c i k‖ ≤ 1) :
    ∃ S : Linfty 𝕜 →L[𝕜] Linfty 𝕜,
      ∀ i : ℕ, S (e i) = finiteVector (s i) (c i) := by
  classical
  -- p k is the (unique, when it exists) block containing coordinate k.
  let p : ℕ → ℕ := fun k =>
    if h : ∃ i : ℕ, k ∈ s i then Classical.choose h else 0
  let w : ℕ → 𝕜 := fun k =>
    if ∃ i : ℕ, k ∈ s i then c (p k) k else 0
  have hw (k : ℕ) : ‖w k‖ ≤ 1 := by
    dsimp [w]
    by_cases h : ∃ i : ℕ, k ∈ s i
    · simpa only [ite_eq_left h] using hc (p k) k
    · simp [h]
  have hbound (a : Linfty 𝕜) (k : ℕ) :
      ‖w k * a (p k)‖ ≤ ‖a‖ := by
    calc
      ‖w k * a (p k)‖ = ‖w k‖ * ‖a (p k)‖ := norm_mul _ _
      _ ≤ 1 * ‖a‖ :=
        mul_le_mul (hw k) (BoundedContinuousFunction.norm_coe_le_norm a (p k))
          (norm_nonneg _) (by positivity)
      _ = ‖a‖ := one_mul _
  let L : Linfty 𝕜 →ₗ[𝕜] Linfty 𝕜 :=
    { toFun := fun a =>
        BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
          (fun k => w k * a (p k)) ‖a‖ (hbound a)
      map_add' := by
        intro a b
        apply BoundedContinuousFunction.ext
        intro k
        change w k * (a (p k) + b (p k)) =
          w k * a (p k) + w k * b (p k)
        exact mul_add _ _ _
      map_smul' := by
        intro t a
        apply BoundedContinuousFunction.ext
        intro k
        change w k * (t * a (p k)) = t * (w k * a (p k))
        exact mul_left_comm _ _ _ }
  have hL (a : Linfty 𝕜) : ‖L a‖ ≤ 1 * ‖a‖ := by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg a)).2
    intro k
    exact hbound a k
  refine ⟨L.mkContinuous 1 hL, ?_⟩
  intro i
  apply BoundedContinuousFunction.ext
  intro k
  change w k * (e i) (p k) = finiteVector (s i) (c i) k
  rw [finiteVector_apply, e_apply]
  by_cases hk : k ∈ s i
  · have hex : ∃ j : ℕ, k ∈ s j := ⟨i, hk⟩
    have hp : p k = i := by
      dsimp [p]
      rw [dite_eq_left hex]
      exact hs _ _ k (Classical.choose_spec hex) hk
    simp [hk, w, hex, hp]
  · by_cases hex : ∃ j : ℕ, k ∈ s j
    · have hpk : k ∈ s (p k) := by
        dsimp [p]
        rw [dite_eq_left hex]
        exact Classical.choose_spec hex
      have hp : p k ≠ i := by
        intro h
        exact hk (h ▸ hpk)
      simp [hk, hp]
    · simp [w, hex, hk]
/-! ## Step 4: uniform smallness of all finite sums (gliding hump) -/

/-- Eventually, `Σ_{k ∈ s} |μ_n(e_k)| < ε` for *all* finite sets `s` at once.
Otherwise one selects late rows `r_j` and pairwise disjoint finite blocks `B_j` with
`Σ_{k ∈ B_j} |μ_{r_j}(e_k)| ≥ ε/2`; encoding the blocks (with phases) by one operator `S`,
the functionals `ν_j = μ_{r_j} ∘ S` contradict the diagonal statement of Step 1. -/
theorem finite_sum_eventually_small
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => μ n a) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : Finset ℕ, (∑ k ∈ s, ‖μ n (e k)‖) < ε := by
  classical
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ s : Finset ℕ, ε ≤ ∑ k ∈ s, ‖μ n (e k)‖ := by
    push Not at hnot
    exact hnot
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  -- A fixed finite set of coordinates has total mass tending to zero.
  have hfinite (F : Finset ℕ) :
      Tendsto (fun n => ∑ k ∈ F, ‖μ n (e k)‖) atTop (𝓝 (0 : ℝ)) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert k F hk ih =>
        have hkzero : Tendsto (fun n => ‖μ n (e k)‖) atTop (𝓝 (0 : ℝ)) := by
          simpa only [norm_zero] using (hμ (e k)).norm
        simpa only [Finset.sum_insert hk, add_zero] using hkzero.add ih
  -- After excluding any finite set F, a sufficiently late bad functional
  -- still has a finite block of mass at least δ outside F.
  have hstep : ∀ (F : Finset ℕ) (N : ℕ),
      ∃ (n : ℕ) (s : Finset ℕ), N ≤ n ∧
        (∀ k ∈ s, k ∉ F) ∧ δ ≤ ∑ k ∈ s, ‖μ n (e k)‖ := by
    intro F N
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 (hfinite F)) δ hδ
    obtain ⟨n, hn, t, ht⟩ := hbad (max N K)
    have hnN : N ≤ n := (le_max_left N K).trans hn
    have hnK : K ≤ n := (le_max_right N K).trans hn
    have hFnonneg : 0 ≤ ∑ k ∈ F, ‖μ n (e k)‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hFsmall : (∑ k ∈ F, ‖μ n (e k)‖) < δ := by
      simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hFnonneg]
        using hK n hnK
    have hsubset : t ⊆ F ∪ (t \ F) := by
      intro k hk
      by_cases hkF : k ∈ F
      · exact Finset.mem_union.mpr (Or.inl hkF)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hk, hkF⟩))
    have hdisj : Disjoint F (t \ F) := by
      apply Finset.disjoint_left.mpr
      intro k hkF hkt
      exact (Finset.mem_sdiff.mp hkt).2 hkF
    have hmass : (∑ k ∈ t, ‖μ n (e k)‖) ≤
        (∑ k ∈ F, ‖μ n (e k)‖) + (∑ k ∈ t \ F, ‖μ n (e k)‖) := by
      calc
        (∑ k ∈ t, ‖μ n (e k)‖) ≤
            ∑ k ∈ F ∪ (t \ F), ‖μ n (e k)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun _ _ _ => norm_nonneg _)
        _ = (∑ k ∈ F, ‖μ n (e k)‖) + (∑ k ∈ t \ F, ‖μ n (e k)‖) :=
          Finset.sum_union hdisj
    refine ⟨n, t \ F, hnN, ?_, ?_⟩
    · intro k hk
      exact (Finset.mem_sdiff.mp hk).2
    · dsimp [δ] at hFsmall ⊢
      linarith only [ht, hFsmall, hmass]
  choose pick block hpick havoid hmass using hstep
  -- F i is the union of the blocks selected before stage i.
  let F : ℕ → Finset ℕ := Nat.rec ∅ (fun i F => F ∪ block F i)
  let s : ℕ → Finset ℕ := fun i => block (F i) i
  let r : ℕ → ℕ := fun i => pick (F i) i
  have hFs (i : ℕ) : F (i + 1) = F i ∪ s i := rfl
  have hFmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro i
    rw [hFs]
    exact Finset.subset_union_left
  have hsF (i : ℕ) : s i ⊆ F (i + 1) := by
    rw [hFs]
    exact Finset.subset_union_right
  have hsavoid (i k : ℕ) (hk : k ∈ s i) : k ∉ F i :=
    havoid (F i) i k hk
  have hs : ∀ i j k : ℕ, k ∈ s i → k ∈ s j → i = j := by
    intro i j k hi hj
    rcases lt_trichotomy i j with hij | hij | hji
    · exact False.elim
        (hsavoid j k hj (hFmono (Nat.succ_le_of_lt hij) (hsF i hi)))
    · exact hij
    · exact False.elim
        (hsavoid i k hi (hFmono (Nat.succ_le_of_lt hji) (hsF j hj)))
  have hr (i : ℕ) : i ≤ r i := hpick (F i) i
  have hr_top : Tendsto r atTop atTop :=
    tendsto_atTop_mono hr tendsto_id
  have hlarge (i : ℕ) : δ ≤ ∑ k ∈ s i, ‖μ (r i) (e k)‖ :=
    hmass (F i) i
  let c : ℕ → ℕ → 𝕜 := fun i k => phase (μ (r i) (e k))
  obtain ⟨S, hS⟩ := exists_block_operator s hs c (fun i k => norm_phase_le _)
  let ν : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜) := fun i => (μ (r i)).comp S
  have hν : ∀ a : Linfty 𝕜, Tendsto (fun i => ν i a) atTop (𝓝 0) := by
    intro a
    change Tendsto (fun i => μ (r i) (S a)) atTop (𝓝 0)
    exact (hμ (S a)).comp hr_top
  have hνlarge (i : ℕ) : δ ≤ ‖ν i (e i)‖ := by
    change δ ≤ ‖μ (r i) (S (e i))‖
    rw [hS i]
    change δ ≤ ‖μ (r i) (finiteVector (s i)
      (fun k => phase (μ (r i) (e k))))‖
    rw [norm_eval_finiteVector]
    exact hlarge i
  -- Contradiction with the diagonal statement (Step 1).
  have hdiag := diagonal_tendsto_zero ν hν
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hdiag) δ hδ
  have hsmall : ‖ν N (e N)‖ < δ := by
    simpa only [dist_zero_right] using hN N (le_refl N)
  exact (not_lt_of_ge (hνlarge N)) hsmall
/-! ## Lemma 2.2 -/

/-- Main conclusion of Lemma 2.2: `Σ_k |μ_n(e_k)| → 0` (each series converges by
`summable_norm_eval`). -/
theorem tsum_norm_tendsto_zero
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => μ n a) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' k : ℕ, ‖μ n (e k)‖) atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := finite_sum_eventually_small μ hμ (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hnonneg : 0 ≤ ∑' k : ℕ, ‖μ n (e k)‖ :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hupper : (∑' k : ℕ, ‖μ n (e k)‖) ≤ ε / 2 :=
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
      (fun s => le_of_lt (hN n hn s))
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  linarith only [hε, hupper]
/-- **Lemma 2.2** (`lem:Phillips`, Phillips' lemma), over `ℝ` or `ℂ`. Let `(μ_n)` be bounded
linear functionals on `ℓ^∞(ℕ)` with `μ_n(a) → 0` for every `a ∈ ℓ^∞(ℕ)`. Then, for every
`n`, the series `Σ_k |μ_n(e_k)|` converges, `Σ_k |μ_n(e_k)| → 0`, and in particular
`μ_n(e_n) → 0`. -/
theorem full
    (μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜))
    (hμ : ∀ a : Linfty 𝕜, Tendsto (fun n => μ n a) atTop (𝓝 0)) :
    (∀ n : ℕ, Summable (fun k : ℕ => ‖μ n (e k)‖)) ∧
      Tendsto (fun n => ∑' k : ℕ, ‖μ n (e k)‖) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => μ n (e n)) atTop (𝓝 0) := by
  have hs (n : ℕ) := summable_norm_eval (μ n)
  have ht := tsum_norm_tendsto_zero μ hμ
  refine ⟨hs, ht, ?_⟩
  refine squeeze_zero_norm (a := fun n => ∑' k : ℕ, ‖μ n (e k)‖) ?_ ht
  intro n
  exact (hs n).le_tsum n (fun _ _ => norm_nonneg _)
/-- Lemma 2.2 for real scalars, written with absolute values as in the paper. -/
theorem tsum_abs_tendsto_zero
    (μ : ℕ → (Linfty ℝ →L[ℝ] ℝ))
    (hμ : ∀ a : Linfty ℝ, Tendsto (fun n => μ n a) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' k : ℕ, |μ n (e k)|) atTop (𝓝 (0 : ℝ)) := by
  simpa only [Real.norm_eq_abs] using tsum_norm_tendsto_zero μ hμ
end Phillips

namespace Phillips

open Filter
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ## Lemma 2.3 -/

/-- Vector-valued version of `diagonal_tendsto_zero`: if `A_n a → 0` for every `a ∈ ℓ^∞`,
then `‖A_n e_n‖ → 0`. (A norming functional is chosen for each `A_n e_n`.) -/
theorem norm_diagonal_tendsto_zero
    (A : ℕ → (Linfty 𝕜 →L[𝕜] X))
    (hA : ∀ a : Linfty 𝕜,
      Tendsto (fun n => A n a) atTop (𝓝 0)) :
    Tendsto (fun n => ‖A n (e n)‖) atTop (𝓝 0) := by
  classical
  -- Choose a norming functional for each diagonal vector.
  choose φ hφnorm hφeval using
    (fun n : ℕ => exists_dual_vector'' 𝕜 (A n (e n)))
  let μ : ℕ → (Linfty 𝕜 →L[𝕜] 𝕜) :=
    fun n => (φ n).comp (A n)
  -- The scalar functionals converge pointwise to zero.
  have hμ : ∀ a : Linfty 𝕜,
      Tendsto (fun n => μ n a) atTop (𝓝 0) := by
    intro a
    refine squeeze_zero_norm (a := fun n => ‖A n a‖) ?_ ?_
    · intro n
      change ‖φ n (A n a)‖ ≤ ‖A n a‖
      calc
        ‖φ n (A n a)‖ ≤ ‖φ n‖ * ‖A n a‖ :=
          (φ n).le_opNorm _
        _ ≤ 1 * ‖A n a‖ :=
          mul_le_mul_of_nonneg_right (hφnorm n) (norm_nonneg _)
        _ = ‖A n a‖ := one_mul _
    · simpa only [norm_zero] using (hA a).norm
  -- Taking norms recovers the norms of the diagonal vectors.
  have hnorm (n : ℕ) : ‖μ n (e n)‖ = ‖A n (e n)‖ := by
    change ‖φ n (A n (e n))‖ = ‖A n (e n)‖
    rw [hφeval n]
    exact RCLike.norm_of_nonneg (norm_nonneg _)
  simpa only [hnorm, norm_zero] using
    (diagonal_tendsto_zero μ hμ).norm
/-- **Lemma 2.3** (`lem:cor-Phillips`). Let `S : ℓ^∞ → X` be a bounded operator and
`t n ≥ 0` with `t n → 0`. Then `‖(T (t n) - Id) (S (e n))‖ → 0`.

Only strong right-continuity of `T` at zero is required; the semigroup law and
completeness of `X` are not used. -/
theorem uniform
    (S : Linfty 𝕜 →L[𝕜] X)
    (T : ℝ → (X →L[𝕜] X))
    (hT : ∀ x : X,
      Tendsto (fun s : ℝ => T s x)
        (nhdsWithin 0 (Set.Ici 0)) (𝓝 x))
    (t : ℕ → ℝ)
    (ht_nonneg : ∀ n : ℕ, 0 ≤ t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        ‖(T (t n) - ContinuousLinearMap.id 𝕜 X) (S (e n))‖)
      atTop (𝓝 0) := by
  have htWithin :
      Tendsto t atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) :=
    tendsto_nhdsWithin_iff.2
      ⟨ht, Filter.Eventually.of_forall (fun n => ht_nonneg n)⟩
  refine norm_diagonal_tendsto_zero
    (fun n => (T (t n) - ContinuousLinearMap.id 𝕜 X).comp S) ?_
  intro a
  have hTa :
      Tendsto (fun n => T (t n) (S a)) atTop (𝓝 (S a)) :=
    (hT (S a)).comp htWithin
  change Tendsto (fun n => T (t n) (S a) - S a) atTop (𝓝 0)
  simpa only [sub_self] using
    (hTa.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => S a) atTop (𝓝 (S a))))
end Phillips

end
end

end AbstractLinearControl
