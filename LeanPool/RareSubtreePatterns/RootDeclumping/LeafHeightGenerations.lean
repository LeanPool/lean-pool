/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RootDeclumping.Generations
public import LeanPool.RareSubtreePatterns.RootDeclumping.ParentFormula
public import LeanPool.RareSubtreePatterns.LeafHeight.Tree


/-!
# The tree conditioned on `λ_∅ ≥ k`: tilted offspring laws and generation sizes

The tree-law part of the proof of Lemma `lem:S_lh` (source lines 3066–3114, inventory P23).
Write `π_s = P(λ_∅(𝒯) ≥ s)` (`piSeq`), `P_k = P(· | λ_∅(𝒯) ≥ k)`, `Z_i = genCount i`,
`C_k = skelSize k = Z_0 + ⋯ + Z_{k-1}`, `L_k = Z_k`.

* `cond_rootDegree_children_mem_tilt`: for `s ≥ 1`, under `P_s` the root has `j` children with
  probability `μ̃_s(j) = μ_j π_{s-1}^j / π_s` (`tiltLaw`, `j ≥ 1`), and the child subtrees are
  then independent with law `P_{s-1}`; `hasSum_tiltLaw`, `hasSum_mul_tiltLaw`: `μ̃_s` is a
  probability law with mean `m_s = π_{s-1} g'(π_{s-1}) / π_s` (`tiltMean`).
* `lintegral_genCount_cond_eq`: `E_k[Z_i] = m_k m_{k-1} ⋯ m_{k-i+1}` for `i ≤ k`, obtained from the
  depth-one many-to-one formula `setLIntegral_sum_children`.
* `tiltMean_le`: `m_s ≤ κ exp(π_{s-1}/(κ μ_κ))`; `lintegral_genCount_cond_le`: one `C > 0` with
  `E_k[Z_i] ≤ C κ^i` uniformly in `0 ≤ i ≤ k` (`≤ C` when `κ = 1`), using `∑_s π_s ≤ 1/μ_0`.
* `lintegral_skelSize_add_genCount_cond_le`: `E_k[C_k + L_k] ≤ C k` (`κ = 1`, `k ≥ 1`) and
  `≤ C κ^k` (`κ ≥ 2`).

The paper's estimates `m_s = 1 + O(π_{s-1})` (`κ = 1`) and `m_s = κ + O(π_{s-1})` (`κ ≥ 2`)
are replaced by the explicit bound `m_s ≤ κ + π_{s-1}/μ_κ ≤ κ exp(π_{s-1}/(κ μ_κ))`, which
gives the same uniform constant.
-/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping
namespace RootDeclumping

open PlaneTree LeafHeight

variable {μ : PMF ℕ}

/-- `∫⁻ F d𝐏_μ = ∑_T 𝐏_μ(T) F(T)`. -/
theorem lintegral_bienayme (μ : PMF ℕ) (F : PlaneTree → ℝ≥0∞) :
    ∫⁻ T, F T ∂(bienayme μ) = ∑' T, weight μ T * F T := by
  rw [bienayme, lintegral_sum_measure]
  refine tsum_congr fun T => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem setLIntegral_bienayme (μ : PMF ℕ) (A : Set PlaneTree) (F : PlaneTree → ℝ≥0∞) :
    ∫⁻ T in A, F T ∂(bienayme μ) = ∑' T, weight μ T * A.indicator F T := by
  rw [← lintegral_indicator (DiscreteMeasurableSpace.forall_measurableSet A), lintegral_bienayme]

/-- `∏_{l} (if l = i then X else Y) = X Y^{d-1}`. -/
theorem prod_ite_eq_mul_pow {d : ℕ} (i : Fin d) (X Y : ℝ≥0∞) :
    ∏ l : Fin d, (if l = i then X else Y) = X * Y ^ (d - 1) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ite_eq_left rfl,
    Finset.prod_congr rfl (fun l hl => ite_eq_right (Finset.ne_of_mem_erase hl)),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

variable (μ) in
/-- The derivative of the offspring generating function, `G'_μ(s) = ∑_d d μ_d s^{d-1}`, in
`ℝ≥0∞`. -/
noncomputable def pgfDeriv (s : ℝ≥0∞) : ℝ≥0∞ := ∑' d, μ d * d * s ^ (d - 1)

/-- Many-to-one formula at depth one (branching property): for `h ≥ 0` and a set `A`,
`E[∑_{u ∈ Γ_∅} h(𝒯_u); all children in A] = G'_μ(P(A)) E[h(𝒯); A]`. -/
theorem setLIntegral_sum_children (μ : PMF ℕ) (h : PlaneTree → ℝ≥0∞) (A : Set PlaneTree) :
    ∫⁻ T in {T | ∀ U ∈ T.children, U ∈ A}, (T.children.map h).sum ∂(bienayme μ) =
      pgfDeriv μ (bienayme μ A) * ∫⁻ U in A, h U ∂(bienayme μ) := by
  rw [setLIntegral_bienayme, setLIntegral_bienayme, pgfDeriv, ← ENNReal.tsum_mul_right,
    ← equivSigma.symm.tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun d => ?_
  set X := ∑' U, weight μ U * A.indicator h U with hX
  set Y := bienayme μ A with hYdef
  have hY : ∑' U, weight μ U * A.indicator 1 U = Y := by
    rw [hYdef, bienayme_apply]
    refine tsum_congr fun U => ?_
    by_cases hU : U ∈ A <;> simp [hU]
  have key : ∀ f : Fin d → PlaneTree,
      weight μ (equivSigma.symm ⟨d, f⟩) *
          {T : PlaneTree | ∀ U ∈ T.children, U ∈ A}.indicator
            (fun T => (T.children.map h).sum) (equivSigma.symm ⟨d, f⟩) =
        μ d * ∑ i : Fin d, ∏ l : Fin d,
          (weight μ (f l) * A.indicator 1 (f l) * (if l = i then h (f l) else 1)) := by
    intro f
    simp only [equivSigma_symm_apply, weight_node_ofFn]
    by_cases hf : ∀ l, f l ∈ A
    · rw [Set.indicator_of_mem (show node (List.ofFn f) ∈
          {T : PlaneTree | ∀ U ∈ T.children, U ∈ A} by simpa [List.mem_ofFn] using hf)]
      simp only [children_node, List.map_ofFn, List.sum_ofFn, Function.comp_def]
      rw [mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      simp [Set.indicator_of_mem (hf _), Finset.prod_ite_eq']
    · rw [Set.indicator_of_notMem (show node (List.ofFn f) ∉
          {T : PlaneTree | ∀ U ∈ T.children, U ∈ A} by simpa [List.mem_ofFn] using hf),
        mul_zero]
      push Not at hf
      obtain ⟨l, hl⟩ := hf
      symm
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [Set.indicator_of_notMem hl])
  simp only [key]
  rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have hpi : ∀ i : Fin d, ∑' f : Fin d → PlaneTree, ∏ l : Fin d,
      (weight μ (f l) * A.indicator 1 (f l) * (if l = i then h (f l) else 1)) =
      ∏ l : Fin d, ∑' U, weight μ U * A.indicator 1 U * (if l = i then h U else 1) := fun i =>
    tsum_pi_fin_prod d (fun l U => weight μ U * A.indicator 1 U * (if l = i then h U else 1))
  simp only [hpi]
  have hfac : ∀ i l : Fin d, ∑' U, weight μ U * A.indicator 1 U * (if l = i then h U else 1) =
      if l = i then X else Y := by
    intro i l
    by_cases hli : l = i
    · simp only [hli, ite_true, hX]
      refine tsum_congr fun U => ?_
      by_cases hU : U ∈ A <;> simp [hU]
    · simp only [hli, ite_false, mul_one, hY]
  simp only [hfac, prod_ite_eq_mul_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring


/-! ### Expected generation sizes on `{λ_∅ ≥ k}` -/

/-- `𝐏_μ(λ_∅ ≥ k) = π_k`, in `ℝ≥0∞`. -/
theorem bienayme_le_rootLeafHeight (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    bienayme μ {T | k ≤ rootLeafHeight T} = ENNReal.ofReal (piSeq μ k) := by
  rw [← bienayme_real_le_rootLeafHeight hc h1, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The recursion `E[Z_{i+1}; λ_∅ ≥ k + 1] = G'_μ(π_k) E[Z_i; λ_∅ ≥ k]`: on `{λ_∅ ≥ k + 1}`
there is no leaf among the first generations, and the children are independent. -/
theorem setLIntegral_genCount_succ (μ : PMF ℕ) (i k : ℕ) :
    ∫⁻ T in {T | k + 1 ≤ rootLeafHeight T}, (genCount (i + 1) T : ℝ≥0∞) ∂(bienayme μ) =
      pgfDeriv μ (bienayme μ {T | k ≤ rootLeafHeight T}) *
        ∫⁻ T in {T | k ≤ rootLeafHeight T}, (genCount i T : ℝ≥0∞) ∂(bienayme μ) := by
  rw [← setLIntegral_sum_children]
  rw [← lintegral_indicator (DiscreteMeasurableSpace.forall_measurableSet _),
    ← lintegral_indicator (DiscreteMeasurableSpace.forall_measurableSet _)]
  congr 1
  funext T
  cases T with
  | node ts =>
    by_cases hall : ∀ U ∈ ts, k ≤ rootLeafHeight U
    · rw [Set.indicator_of_mem (s := {T : PlaneTree | ∀ U ∈ T.children,
          U ∈ {V : PlaneTree | k ≤ rootLeafHeight V}}) (by simpa using hall)]
      by_cases hts : ts = []
      · subst hts
        rw [Set.indicator_of_notMem (by simp)]
        simp
      · rw [Set.indicator_of_mem (show node ts ∈ {T : PlaneTree | k + 1 ≤ rootLeafHeight T} from
            (succ_le_rootLeafHeight_iff k (node ts)).mpr ⟨hts, hall⟩),
          genCount_succ_node, Nat.cast_list_sum, List.map_map]
        rfl
    · rw [Set.indicator_of_notMem (s := {T : PlaneTree | ∀ U ∈ T.children,
          U ∈ {V : PlaneTree | k ≤ rootLeafHeight V}}) (by simpa using hall),
        Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq, succ_le_rootLeafHeight_iff, children_node, not_and]
      exact fun _ => hall

variable (μ) in
/-- `x g'(x) = ∑_d d μ_d x^d` (real). -/
noncomputable def xgDeriv (x : ℝ) : ℝ := ∑' d : ℕ, (d : ℝ) * mass μ d * x ^ d

theorem summable_xgDeriv (hc : IsCritical μ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Summable (fun d : ℕ => (d : ℝ) * mass μ d * x ^ d) :=
  Summable.of_nonneg_of_le (fun d => mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (mass_nonneg d))
      (pow_nonneg hx0 d))
    (fun d => mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg d) (mass_nonneg d))
      (pow_le_one₀ hx0 hx1)) (hasSum_mean hc).summable

theorem xgDeriv_nonneg {x : ℝ} (hx0 : 0 ≤ x) : 0 ≤ xgDeriv μ x :=
  tsum_nonneg fun d => mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (mass_nonneg d))
    (pow_nonneg hx0 d)

/-- `x G'_μ(x) = x g'(x)`, comparing the `ℝ≥0∞` and real versions. -/
theorem ofReal_mul_pgfDeriv (hc : IsCritical μ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ENNReal.ofReal x * pgfDeriv μ (ENNReal.ofReal x) = ENNReal.ofReal (xgDeriv μ x) := by
  rw [pgfDeriv, ← ENNReal.tsum_mul_left, xgDeriv,
    ENNReal.ofReal_tsum_of_nonneg (fun d => mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
      (mass_nonneg d)) (pow_nonneg hx0 d)) (summable_xgDeriv hc hx0 hx1)]
  refine tsum_congr fun d => ?_
  rw [show μ d = ENNReal.ofReal (mass μ d) from (ENNReal.ofReal_toReal (μ.apply_ne_top d)).symm,
    ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg d) (mass_nonneg d)),
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_pow hx0, ENNReal.ofReal_natCast]
  rcases d with _ | d
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    ring

variable (μ) in
/-- The mean `m_s = π_{s-1} g'(π_{s-1}) / π_s` of the tilted offspring law `μ̃_s` (source lines
3088–3096). -/
noncomputable def tiltMean (s : ℕ) : ℝ := xgDeriv μ (piSeq μ (s - 1)) / piSeq μ s

theorem tiltMean_nonneg (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (s : ℕ) : 0 ≤ tiltMean μ s :=
  div_nonneg (xgDeriv_nonneg (piSeq_pos hc h1 _).le) (piSeq_pos hc h1 s).le

/-- Exact first moments: for `i ≤ k`,
`E[Z_i(𝒯); λ_∅(𝒯) ≥ k] = π_k m_k m_{k-1} ⋯ m_{k-i+1}`. -/
theorem setLIntegral_genCount_eq (hc : IsCritical μ) (h1 : μ 1 ≠ 1) {i k : ℕ} (hik : i ≤ k) :
    ∫⁻ T in {T | k ≤ rootLeafHeight T}, (genCount i T : ℝ≥0∞) ∂(bienayme μ) =
      ENNReal.ofReal (piSeq μ k * ∏ j ∈ Finset.range i, tiltMean μ (k - j)) := by
  induction i generalizing k with
  | zero =>
    simp only [genCount_zero, Nat.cast_one, lintegral_const, Measure.restrict_apply_univ,
      one_mul, Finset.range_zero, Finset.prod_empty, mul_one]
    exact bienayme_le_rootLeafHeight hc h1 k
  | succ i ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk0 := piSeq_pos hc h1 k
    have hk1 := piSeq_le_one hc h1 k
    have hk' := piSeq_pos hc h1 (k + 1)
    rw [setLIntegral_genCount_succ, ih (by omega), bienayme_le_rootLeafHeight hc h1,
      ENNReal.ofReal_mul hk0.le, ← mul_assoc, mul_comm (pgfDeriv μ _),
      ofReal_mul_pgfDeriv hc hk0.le hk1, ← ENNReal.ofReal_mul (xgDeriv_nonneg hk0.le),
      Finset.prod_range_succ']
    congr 1
    simp only [Nat.add_sub_add_right, Nat.sub_zero, tiltMean, Nat.add_sub_cancel]
    field_simp

/-- **Expected generation sizes under `P_k = P(· | λ_∅ ≥ k)`** (source lines 3097–3107):
for `i ≤ k`, `E_k[Z_i] = m_k m_{k-1} ⋯ m_{k-i+1}`. -/
theorem lintegral_genCount_cond_eq (hc : IsCritical μ) (h1 : μ 1 ≠ 1) {i k : ℕ} (hik : i ≤ k) :
    ∫⁻ T, (genCount i T : ℝ≥0∞) ∂(cond (bienayme μ) {T | k ≤ rootLeafHeight T}) =
      ENNReal.ofReal (∏ j ∈ Finset.range i, tiltMean μ (k - j)) := by
  have hk0 := piSeq_pos hc h1 k
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    setLIntegral_genCount_eq hc h1 hik, bienayme_le_rootLeafHeight hc h1,
    ENNReal.ofReal_mul hk0.le, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hk0).ne' ENNReal.ofReal_ne_top, one_mul]


/-! ### Bounds on the tilted means and the generation sizes -/

/-- `x g'(x) ≤ κ μ_κ x^κ + x^{κ+1}` on `[0, 1]` (critical `μ`). -/
theorem xgDeriv_le (hc : IsCritical μ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    xgDeriv μ x ≤ kappa μ * mass μ (kappa μ) * x ^ kappa μ + x ^ (kappa μ + 1) := by
  have hu : HasSum (fun d : ℕ => (if d = kappa μ then
      (kappa μ : ℝ) * mass μ (kappa μ) * x ^ kappa μ else 0) + (d : ℝ) * mass μ d *
        x ^ (kappa μ + 1))
      ((kappa μ : ℝ) * mass μ (kappa μ) * x ^ kappa μ + 1 * x ^ (kappa μ + 1)) :=
    (hasSum_ite_eq (kappa μ) _).add ((hasSum_mean hc).mul_right _)
  rw [one_mul] at hu
  refine hasSum_le (fun d => ?_) (summable_xgDeriv hc hx0 hx1).hasSum hu
  have hdm : 0 ≤ (d : ℝ) * mass μ d := mul_nonneg (Nat.cast_nonneg d) (mass_nonneg d)
  rcases lt_trichotomy d (kappa μ) with hd | rfl | hd
  · rw [ite_eq_right hd.ne]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp
    · rw [mass_eq_zero_of_lt_kappa hd0 hd]
      simp
  · rw [ite_eq_left rfl]
    have := mul_nonneg hdm (pow_nonneg hx0 (kappa μ + 1))
    linarith
  · rw [ite_eq_right hd.ne', zero_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 hd) hdm

/-- `m_s ≤ κ exp(π_{s-1} / (κ μ_κ))` for `s ≥ 1`: since `π_s = g(π_{s-1}) ≥ μ_κ π_{s-1}^κ`,
`m_s ≤ κ + π_{s-1}/μ_κ` (source lines 3097–3101: `m_s = κ + O(π_{s-1})`). -/
theorem tiltMean_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) {s : ℕ} (hs : 1 ≤ s) :
    tiltMean μ s ≤ kappa μ * Real.exp (piSeq μ (s - 1) / (kappa μ * mass μ (kappa μ))) := by
  set x := piSeq μ (s - 1)
  set κ := kappa μ
  set m := mass μ κ
  have hx0 : 0 < x := piSeq_pos hc h1 _
  have hx1 : x ≤ 1 := piSeq_le_one hc h1 _
  have hm : 0 < m := mass_kappa_pos hc h1
  have hκ : (1 : ℝ) ≤ κ := by exact_mod_cast one_le_kappa hc h1
  have hs' : piSeq μ s = g μ x := by
    have : piSeq μ s = piSeq μ ((s - 1) + 1) := by rw [Nat.sub_add_cancel hs]
    rw [this, piSeq_succ]
  have hg : m * x ^ κ ≤ g μ x := (g_bounds hc h1 hx0.le hx1).1
  have hgpos : 0 < g μ x := lt_of_lt_of_le (mul_pos hm (pow_pos hx0 _)) hg
  rw [tiltMean, hs', div_le_iff₀ hgpos]
  have hexp : 1 + x / (κ * m) ≤ Real.exp (x / (κ * m)) := by
    linarith [Real.add_one_le_exp (x / (κ * m))]
  calc xgDeriv μ x ≤ κ * m * x ^ κ + x ^ (κ + 1) := xgDeriv_le hc hx0.le hx1
    _ = κ * (1 + x / (κ * m)) * (m * x ^ κ) := by
        field_simp
        ring
    _ ≤ κ * Real.exp (x / (κ * m)) * (m * x ^ κ) := by gcongr
    _ ≤ κ * Real.exp (x / (κ * m)) * g μ x := by gcongr

/-- `m_k m_{k-1} ⋯ m_{k-i+1} ≤ C κ^i` uniformly in `0 ≤ i ≤ k`, with
`C = exp(1/(μ_0 κ μ_κ))`, because `∑_s π_s ≤ 1/μ_0` (source lines 3097–3107). -/
theorem prod_tiltMean_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) {i k : ℕ} (hik : i ≤ k) :
    ∏ j ∈ Finset.range i, tiltMean μ (k - j) ≤
      Real.exp (1 / (mass μ 0 * (kappa μ * mass μ (kappa μ)))) * (kappa μ : ℝ) ^ i := by
  set c := (kappa μ : ℝ) * mass μ (kappa μ)
  have hc0 : 0 < c := mul_pos (by exact_mod_cast (one_le_kappa hc h1)) (mass_kappa_pos hc h1)
  have h0 := mass_zero_pos hc h1
  calc ∏ j ∈ Finset.range i, tiltMean μ (k - j)
      ≤ ∏ j ∈ Finset.range i, ((kappa μ : ℝ) * Real.exp (piSeq μ (k - 1 - j) / c)) := by
        refine Finset.prod_le_prod₀ (fun j _ => tiltMean_nonneg hc h1 _) (fun j hj => ?_)
        have hj := Finset.mem_range.mp hj
        have := tiltMean_le hc h1 (s := k - j) (by omega)
        rwa [show k - j - 1 = k - 1 - j by omega] at this
    _ = Real.exp (∑ j ∈ Finset.range i, piSeq μ (k - 1 - j) / c) * (kappa μ : ℝ) ^ i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Real.exp_sum,
          mul_comm]
    _ ≤ Real.exp (1 / (mass μ 0 * c)) * (kappa μ : ℝ) ^ i := by
        gcongr
        rw [← Finset.sum_div, show 1 / (mass μ 0 * c) = (1 / mass μ 0) / c by rw [div_div],
          div_le_div_iff_of_pos_right hc0]
        calc ∑ j ∈ Finset.range i, piSeq μ (k - 1 - j)
            ≤ ∑ j ∈ Finset.range k, piSeq μ (k - 1 - j) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hik)
                (fun j _ _ => (piSeq_pos hc h1 _).le)
          _ = ∑ j ∈ Finset.range k, piSeq μ j := Finset.sum_range_reflect (piSeq μ) k
          _ ≤ (mass μ 0)⁻¹ := sum_piSeq_le hc h1 k
          _ = 1 / mass μ 0 := (one_div _).symm

/-- **Expected generation sizes** (source lines 3097–3107, inventory P23): there is `C > 0`
such that, uniformly in `0 ≤ i ≤ k`, `E[Z_i(𝒯) | λ_∅(𝒯) ≥ k] ≤ C κ^i` (that is, `≤ C` when
`κ = 1` and `≤ C κ^i` when `κ ≥ 2`). -/
theorem lintegral_genCount_cond_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ i k : ℕ, i ≤ k →
      ∫⁻ T, (genCount i T : ℝ≥0∞) ∂(cond (bienayme μ) {T | k ≤ rootLeafHeight T}) ≤
        ENNReal.ofReal (C * (kappa μ : ℝ) ^ i) :=
  ⟨_, Real.exp_pos _, fun i k hik => by
    rw [lintegral_genCount_cond_eq hc h1 hik]
    exact ENNReal.ofReal_le_ofReal (prod_tiltMean_le hc h1 hik)⟩


/-- `E_k[C_k + L_k] = ∑_{i ≤ k} E_k[Z_i]`. -/
theorem lintegral_skelSize_add_genCount (ν : Measure PlaneTree) (k : ℕ) :
    ∫⁻ T, ((skelSize k T + genCount k T : ℕ) : ℝ≥0∞) ∂ν =
      ∑ i ∈ Finset.range (k + 1), ∫⁻ T, (genCount i T : ℝ≥0∞) ∂ν := by
  rw [← lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete)]
  congr 1
  funext T
  rw [skelSize, ← Finset.sum_range_succ, Nat.cast_sum]

/-- `∑_{i ≤ k} r^i ≤ 2 r^k` for `r ≥ 2`. -/
theorem sum_range_succ_pow_le {r : ℝ} (hr : 2 ≤ r) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), r ^ i ≤ 2 * r ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 0 ≤ r ^ k := pow_nonneg (by linarith) k
    nlinarith

/-- **Skeleton-plus-frontier bound** (source lines 3108–3114, inventory P23): with
`C_k = Z_0 + ⋯ + Z_{k-1}` and `L_k = Z_k`, there is `C > 0` such that
`E[C_k + L_k | λ_∅ ≥ k] ≤ C k` for all `k ≥ 1` if `κ = 1`, and `≤ C κ^k` for all `k` if
`κ ≥ 2`. -/
theorem lintegral_skelSize_add_genCount_cond_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧
      (kappa μ = 1 → ∀ k : ℕ, 1 ≤ k →
        ∫⁻ T, ((skelSize k T + genCount k T : ℕ) : ℝ≥0∞)
            ∂(cond (bienayme μ) {T | k ≤ rootLeafHeight T}) ≤ ENNReal.ofReal (C * k)) ∧
      (2 ≤ kappa μ → ∀ k : ℕ,
        ∫⁻ T, ((skelSize k T + genCount k T : ℕ) : ℝ≥0∞)
            ∂(cond (bienayme μ) {T | k ≤ rootLeafHeight T}) ≤
          ENNReal.ofReal (C * (kappa μ : ℝ) ^ k)) := by
  obtain ⟨C, hC, hb⟩ := lintegral_genCount_cond_le hc h1
  have hsum : ∀ k : ℕ, ∫⁻ T, ((skelSize k T + genCount k T : ℕ) : ℝ≥0∞)
      ∂(cond (bienayme μ) {T | k ≤ rootLeafHeight T}) ≤
        ENNReal.ofReal (C * ∑ i ∈ Finset.range (k + 1), (kappa μ : ℝ) ^ i) := by
    intro k
    rw [lintegral_skelSize_add_genCount, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg _) i))]
    exact Finset.sum_le_sum fun i hi => hb i k (by have := Finset.mem_range.mp hi; omega)
  refine ⟨2 * C, by positivity, fun hκ k hk => ?_, fun hκ k => ?_⟩
  · refine (hsum k).trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [hκ, Nat.cast_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    nlinarith
  · refine (hsum k).trans (ENNReal.ofReal_le_ofReal ?_)
    have := sum_range_succ_pow_le (r := (kappa μ : ℝ)) (by exact_mod_cast hκ) k
    have := mul_le_mul_of_nonneg_left this hC.le
    linarith

/-! ### The tilted offspring law -/

variable (μ) in
/-- The tilted offspring law `μ̃_s(j) = μ_j π_{s-1}^j / π_s` for `j ≥ 1` (and `μ̃_s(0) = 0`)
of a vertex that must remain protected for another `s ≥ 1` generations (source lines
3088–3092). -/
noncomputable def tiltLaw (s j : ℕ) : ℝ :=
  if j = 0 then 0 else mass μ j * piSeq μ (s - 1) ^ j / piSeq μ s

/-- `μ̃_s` is a probability law on `ℕ` (`s ≥ 1`), since `π_s = g(π_{s-1})`. -/
theorem hasSum_tiltLaw (hc : IsCritical μ) (h1 : μ 1 ≠ 1) {s : ℕ} (hs : 1 ≤ s) :
    HasSum (tiltLaw μ s) 1 := by
  set x := piSeq μ (s - 1)
  have hx0 : 0 ≤ x := (piSeq_pos hc h1 _).le
  have hx1 : x ≤ 1 := piSeq_le_one hc h1 _
  have hs' : piSeq μ s = g μ x := by
    have : piSeq μ s = piSeq μ ((s - 1) + 1) := by rw [Nat.sub_add_cancel hs]
    rw [this, piSeq_succ]
  have hpos : 0 < piSeq μ s := piSeq_pos hc h1 s
  have hg : HasSum (fun j : ℕ => if j = 0 then 0 else mass μ j * x ^ j) (g μ x) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ite_true, sub_zero, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ite_false]
    exact (summable_g (μ := μ) hx0 hx1).hasSum
  have := hg.div_const (piSeq μ s)
  rw [← hs', div_self hpos.ne'] at this
  convert this using 1
  funext j
  unfold tiltLaw
  split_ifs
  · simp
  · rfl

/-- The mean of `μ̃_s` is `m_s = π_{s-1} g'(π_{s-1}) / π_s` (`s ≥ 1`, source lines 3093–3096). -/
theorem hasSum_mul_tiltLaw (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (s : ℕ) :
    HasSum (fun j : ℕ => (j : ℝ) * tiltLaw μ s j) (tiltMean μ s) := by
  have hx0 : 0 ≤ piSeq μ (s - 1) := (piSeq_pos hc h1 _).le
  have hx1 : piSeq μ (s - 1) ≤ 1 := piSeq_le_one hc h1 _
  refine ((summable_xgDeriv hc hx0 hx1).hasSum.div_const (piSeq μ s)).congr_fun fun j => ?_
  simp only [tiltLaw]
  split_ifs with hj
  · simp [hj]
  · ring

/-- **The conditional tree law given `λ_∅ ≥ s`** (source lines 3085–3092, inventory P23): for
`s ≥ 1`, under `P(· | λ_∅(𝒯) ≥ s)` the root has `j` children with probability `μ̃_s(j)`, and,
given this, the child subtrees are independent with law `P(· | λ_∅(𝒯) ≥ s - 1)`:
`P(k_∅ = j, 𝒯_i ∈ A_i ∀ i < j | λ_∅ ≥ s) = μ̃_s(j) ∏_{i<j} P(A_i | λ_∅ ≥ s - 1)`.
Iterating, the first `k` generations under `P(· | λ_∅ ≥ k)` form a Galton–Watson tree with the
generation-dependent offspring laws `μ̃_k, μ̃_{k-1}, …, μ̃_1`. -/
theorem cond_rootDegree_children_mem_tilt (hc : IsCritical μ) (h1 : μ 1 ≠ 1) {s : ℕ}
    (hs : 1 ≤ s) (j : ℕ) (A : ℕ → Set PlaneTree) :
    cond (bienayme μ) {T | s ≤ rootLeafHeight T}
        {T | T.rootDegree = j ∧ ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} =
      ENNReal.ofReal (tiltLaw μ s j) *
        ∏ i ∈ Finset.range j, cond (bienayme μ) {T | s - 1 ≤ rootLeafHeight T} (A i) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [cond_apply (DiscreteMeasurableSpace.forall_measurableSet _),
    bienayme_le_rootLeafHeight hc h1]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : {T : PlaneTree | s + 1 ≤ rootLeafHeight T} ∩
        {T | T.rootDegree = 0 ∧ ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} =
        ∅ := by
      ext T
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, succ_le_rootLeafHeight_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hne hdeg
      exact absurd (List.eq_nil_of_length_eq_zero hdeg) hne.1
    rw [this]
    simp [tiltLaw]
  · have hset : {T : PlaneTree | s + 1 ≤ rootLeafHeight T} ∩
        {T | T.rootDegree = j ∧ ∀ (i : ℕ) (hi : i < T.children.length), T.children[i] ∈ A i} =
        {T | T.rootDegree = j ∧ ∀ (i : ℕ) (hi : i < T.children.length),
          T.children[i]'hi ∈ {U | s ≤ rootLeafHeight U} ∩ A i} := by
      ext T
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, succ_le_rootLeafHeight_iff,
        rootDegree]
      constructor
      · rintro ⟨⟨-, hall⟩, hdeg, hA⟩
        exact ⟨hdeg, fun i hi => ⟨hall _ (List.getElem_mem hi), hA i hi⟩⟩
      · rintro ⟨hdeg, hA⟩
        refine ⟨⟨fun h => by simp [h] at hdeg; omega, fun U hU => ?_⟩, hdeg,
          fun i hi => (hA i hi).2⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hU
        exact (hA i hi).1
    have hcond : ∀ i, bienayme μ ({U | s ≤ rootLeafHeight U} ∩ A i) =
        ENNReal.ofReal (piSeq μ s) * cond (bienayme μ) {T | s ≤ rootLeafHeight T} (A i) := by
      intro i
      rw [cond_apply (DiscreteMeasurableSpace.forall_measurableSet _),
        bienayme_le_rootLeafHeight hc h1, ← mul_assoc,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (piSeq_pos hc h1 s)).ne'
          ENNReal.ofReal_ne_top, one_mul]
    rw [hset, bienayme_rootDegree_eq_children_mem, Finset.prod_congr rfl fun i _ => hcond i,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, tiltLaw, ite_eq_right hj.ne',
      Nat.add_sub_cancel, ENNReal.ofReal_div_of_pos (piSeq_pos hc h1 _),
      ENNReal.ofReal_mul (mass_nonneg j), ENNReal.ofReal_pow (piSeq_pos hc h1 s).le,
      show μ j = ENNReal.ofReal (mass μ j) from (ENNReal.ofReal_toReal (μ.apply_ne_top j)).symm,
      div_eq_mul_inv]
    ring

end RootDeclumping
end PoissonDeclumping
