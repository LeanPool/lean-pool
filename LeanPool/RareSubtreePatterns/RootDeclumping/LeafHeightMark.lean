/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RootDeclumping.ParentFormula
public import LeanPool.RareSubtreePatterns.LeafHeight.Tree

/-!
# Leaf-height declumping: the root formula and the conditional mark bound

Section 7.2 of the paper (source lines 3132–3181, 3236–3241; inventory U11 and Lemma
`lem:lh_conditional_mark`). For the leaf-height marks `G_k(T) = 1{λ_∅(T) ≥ k}`, with
`κ = min{j ≥ 1 : μ_j > 0}`, the declumped mark is
`Ghat_k(T) = 1{k_∅(T) ≥ κ + 1} 1{∃ u ∈ Γ_∅(T), λ_∅(T_u) ≥ k}` (`lhDeclumpedMark`).
Write `π_k = P(λ_∅(𝒯) ≥ k)` (`piSeq`, identified by `bienayme_real_le_rootLeafHeight`) and
`π̂_k = P(Ghat_k(𝒯) = 1)`.

* U11: `lh_declumped_prob_eq`: `π̂_k = ∑_{j ≥ κ+1} μ_j (1 - (1 - π_k)^j)`;
  `lh_declumped_sub_isLittleO`, `lh_declumped_tendsto_div`: `π̂_k = c π_k + o(π_k)`,
  `c = 1 - κ μ_κ`; `lh_declumped_isEquivalent`: `π̂_k ∼ c π_k` when `c > 0`;
  `bB_mul_le_lh_declumped`: `π̂_k ≥ b π_k` with `b = P(k_∅ ≥ κ + 1)` (`bB_lhDegrees_eq`),
  and `b > 0` when `c > 0` (`bB_lhDegrees_pos`).
* Lemma `lem:lh_conditional_mark` (`lem_lh_conditional_mark`): one `C > 0` with
  `P(Ghat_k(𝒯) = 1, λ_∅(𝒯) ≥ m) ≤ C π_k π_m` for all `0 ≤ m ≤ k`. The proof computes the left
  side exactly by the branching property, `∑_{d ≥ κ+1} μ_d (π_{m-1}^d - (π_{m-1} - π_k)^d)`,
  which gives the paper's union bound `π_k ∑_{d ≥ κ+1} d μ_d π_{m-1}^{d-1}`; then criticality and
  `π_m ≥ μ_κ π_{m-1}^κ`. The assumption `c > 0` of the surrounding subsection is not needed.
-/

@[expose] public section

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal

namespace PoissonDeclumping
namespace RootDeclumping

open PlaneTree LeafHeight

variable {μ : PMF ℕ}

variable (μ) in
/-- The degree set `B = {j : j ≥ κ + 1}` of the leaf-height declumping (source line 3133). -/
def lhDegrees : Set ℕ := {j | kappa μ + 1 ≤ j}

variable (μ) in
/-- The declumped leaf-height mark `Ghat_k(T) = 1{k_∅(T) ≥ κ + 1} 1{∃ u ∈ Γ_∅(T), λ_∅(T_u) ≥ k}`
(source lines 3132–3137, with `G_k(T) = 1{λ_∅(T) ≥ k}` and `B = {j ≥ κ + 1}`). -/
def lhDeclumpedMark (k : ℕ) : PlaneTree → Prop :=
  declumpedMark (lhDegrees μ) (fun T => k ≤ rootLeafHeight T)

/-- `c_B = c = 1 - κ μ_κ` for `B = {j ≥ κ + 1}` (source line 3031). -/
theorem cBReal_lhDegrees (hc : IsCritical μ) : cBReal μ (lhDegrees μ) = cConst μ := by
  refine (hasSum_cConst hc).tsum_eq.symm ▸ (tsum_congr fun j => ?_)
  simp only [lhDegrees, Set.indicator_apply, Set.mem_ofPred_eq]

/-- U11, the leaf-height declumped root formula (source lines 3134–3141):
`π̂_k = ∑_{j ≥ κ + 1} μ_j (1 - (1 - π_k)^j)`. -/
theorem lh_declumped_prob_eq (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    (bienayme μ).real {T | lhDeclumpedMark μ k T} =
      ∑' j, {j | kappa μ + 1 ≤ j}.indicator
        (fun j => mass μ j * (1 - (1 - piSeq μ k) ^ j)) j := by
  rw [lhDeclumpedMark, parent_formula hc h1, bienayme_real_le_rootLeafHeight hc h1]
  rfl

theorem lh_declumped_prob_eq_parentFun (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    (bienayme μ).real {T | lhDeclumpedMark μ k T} = parentFun μ (lhDegrees μ) (piSeq μ k) := by
  rw [lhDeclumpedMark, parent_formula hc h1, bienayme_real_le_rootLeafHeight hc h1]

/-- U11: `π̂_k - c π_k = o(π_k)` as `k → ∞` (dominated convergence, source line 3142). -/
theorem lh_declumped_sub_isLittleO (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    (fun k => (bienayme μ).real {T | lhDeclumpedMark μ k T} - cConst μ * piSeq μ k)
      =o[atTop] piSeq μ := by
  have hlim : Tendsto (piSeq μ) atTop (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_piSeq_zero hc h1,
      Eventually.of_forall fun k => (piSeq_pos hc h1 k).le⟩
  have h := (parentFun_sub_isLittleO hc (lhDegrees μ)).comp_tendsto hlim
  rw [cBReal_lhDegrees hc] at h
  refine h.congr' (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => rfl)
  simp only [Function.comp_apply, lh_declumped_prob_eq_parentFun hc h1]

/-- U11: `π̂_k / π_k → c` (source line 3142). -/
theorem lh_declumped_tendsto_div (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    Tendsto (fun k => (bienayme μ).real {T | lhDeclumpedMark μ k T} / piSeq μ k) atTop
      (𝓝 (cConst μ)) := by
  have hlim : Tendsto (piSeq μ) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_piSeq_zero hc h1,
      Eventually.of_forall fun k => piSeq_pos hc h1 k⟩
  have h := (tendsto_parentFun_div hc (lhDegrees μ)).comp hlim
  rw [cBReal_lhDegrees hc] at h
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, lh_declumped_prob_eq_parentFun hc h1]

/-- U11: if `c = 1 - κ μ_κ > 0`, then `π̂_k ∼ c π_k` (source line 3142). -/
theorem lh_declumped_isEquivalent (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hcpos : 0 < cConst μ) :
    (fun k => (bienayme μ).real {T | lhDeclumpedMark μ k T}) ~[atTop]
      fun k => cConst μ * piSeq μ k := by
  refine ((lh_declumped_sub_isLittleO hc h1).trans_isBigO ?_)
  refine (isBigO_const_mul_self (cConst μ)⁻¹ (fun k => cConst μ * piSeq μ k) atTop).congr_left
    fun k => ?_
  field_simp

/-- `b = P(k_∅(𝒯) ≥ κ + 1)` is the constant `b_B` of `B = {j ≥ κ + 1}` (source line 3236). -/
theorem bB_lhDegrees_eq (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    bB μ (lhDegrees μ) = (bienayme μ).real {T | kappa μ + 1 ≤ T.rootDegree} := by
  rw [bB_eq_prob hc h1]
  congr 1
  ext T
  simp only [lhDegrees, Set.mem_ofPred_eq, and_iff_left_iff_imp]
  omega

/-- If `c > 0` then `b = P(k_∅(𝒯) ≥ κ + 1) > 0` (source line 3236). -/
theorem bB_lhDegrees_pos (hc : IsCritical μ) (hcpos : 0 < cConst μ) :
    0 < bB μ (lhDegrees μ) := by
  rw [bB_pos_iff_cBReal_pos hc, cBReal_lhDegrees hc]
  exact hcpos

/-- `π̂_k ≥ b π_k` with `b = P(k_∅(𝒯) ≥ κ + 1)` (source lines 3236–3241). -/
theorem bB_mul_le_lh_declumped (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    bB μ (lhDegrees μ) * piSeq μ k ≤ (bienayme μ).real {T | lhDeclumpedMark μ k T} := by
  have := bB_mul_le_declumped hc h1 (lhDegrees μ) (fun T => k ≤ rootLeafHeight T)
  rwa [bienayme_real_le_rootLeafHeight hc h1] at this

/-- `π̂_k ≤ c π_k ≤ π_k`. -/
theorem lh_declumped_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    (bienayme μ).real {T | lhDeclumpedMark μ k T} ≤ cConst μ * piSeq μ k := by
  have := declumped_le_cBReal_mul hc h1 (lhDegrees μ) (fun T => k ≤ rootLeafHeight T)
  rwa [bienayme_real_le_rootLeafHeight hc h1, cBReal_lhDegrees hc] at this


/-! ### Lemma `lem:lh_conditional_mark` -/

/-- The event `{Ghat_k(𝒯) = 1, λ_∅(𝒯) ≥ m + 1}` in product form: root degree `≥ κ + 1`, all
children with leaf-height `≥ m`, some child with leaf-height `≥ k`. -/
theorem lh_mark_and_le_eq (k m : ℕ) :
    {T : PlaneTree | lhDeclumpedMark μ k T ∧ m + 1 ≤ rootLeafHeight T} =
      {T | T.rootDegree ∈ lhDegrees μ ∧
        (∀ U ∈ T.children, U ∈ {V : PlaneTree | m ≤ rootLeafHeight V}) ∧
        ∃ U ∈ T.children, U ∈ {V : PlaneTree | k ≤ rootLeafHeight V}} := by
  ext T
  simp only [lhDeclumpedMark, declumpedMark, Set.mem_ofPred_eq, succ_le_rootLeafHeight_iff]
  constructor
  · rintro ⟨⟨hB, hU⟩, -, hall⟩
    exact ⟨hB, hall, hU⟩
  · rintro ⟨hB, hall, hU⟩
    refine ⟨⟨hB, hU⟩, ?_, hall⟩
    obtain ⟨U, hU, -⟩ := hU
    exact List.ne_nil_of_mem hU

/-- `a^d - b^d ≤ d (a - b) a^κ` for `0 ≤ b ≤ a ≤ 1` and `d ≥ κ + 1`. -/
theorem pow_sub_pow_le_of_le {a b : ℝ} (hb0 : 0 ≤ b) (hba : b ≤ a) (ha1 : a ≤ 1) {d κ : ℕ}
    (hd : κ + 1 ≤ d) : a ^ d - b ^ d ≤ d * (a - b) * a ^ κ := by
  have ha0 : 0 ≤ a := hb0.trans hba
  have h := abs_pow_sub_pow_le a b d
  rw [abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg ha0, abs_of_nonneg hb0,
    max_eq_left hba] at h
  calc a ^ d - b ^ d ≤ |a ^ d - b ^ d| := le_abs_self _
    _ ≤ (a - b) * d * a ^ (d - 1) := h
    _ ≤ (a - b) * d * a ^ κ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ha0 ha1 (by omega))
          (mul_nonneg (sub_nonneg.mpr hba) (Nat.cast_nonneg d))
    _ = d * (a - b) * a ^ κ := by ring

/-- **Lemma `lem:lh_conditional_mark`** (source lines 3148–3181): for a critical `μ` with
`μ_1 ≠ 1`, there is one constant `C > 0` such that, for all `0 ≤ m ≤ k`,
`P(Ghat_k(𝒯) = 1, λ_∅(𝒯) ≥ m) ≤ C π_k π_m`. One can take `C = μ_κ⁻¹`. (The paper states it in a
subsection assuming `c > 0`; that assumption is not needed.) -/
theorem lem_lh_conditional_mark (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m k : ℕ, m ≤ k →
      (bienayme μ).real {T | lhDeclumpedMark μ k T ∧ m ≤ rootLeafHeight T} ≤
        C * piSeq μ k * piSeq μ m := by
  have hκ := mass_kappa_pos hc h1
  have hκ1 : mass μ (kappa μ) ≤ 1 := mass_le_one _
  have hC1 : 1 ≤ (mass μ (kappa μ))⁻¹ := one_le_inv₀ hκ |>.mpr hκ1
  have hc1 : cConst μ ≤ 1 := cBReal_lhDegrees hc ▸ cBReal_le_one hc (lhDegrees μ)
  refine ⟨(mass μ (kappa μ))⁻¹, inv_pos.mpr hκ, fun m k hmk => ?_⟩
  have hπk0 := piSeq_pos hc h1 k
  rcases m with _ | m
  · -- `m = 0`: `P(Ghat_k = 1) = π̂_k ≤ c π_k ≤ π_k`.
    simp only [Nat.zero_le, and_true, piSeq_zero, mul_one]
    calc (bienayme μ).real {T | lhDeclumpedMark μ k T} ≤ cConst μ * piSeq μ k :=
          lh_declumped_le hc h1 k
      _ ≤ 1 * piSeq μ k := by gcongr
      _ ≤ (mass μ (kappa μ))⁻¹ * piSeq μ k := by gcongr
  · -- `m ≥ 1`: union bound over the marked child and criticality.
    set a := piSeq μ m with ha
    have ha0 : 0 ≤ a := (piSeq_pos hc h1 m).le
    have ha1 : a ≤ 1 := piSeq_le_one hc h1 m
    have hka : piSeq μ k ≤ a := antitone_piSeq hc h1 (by omega)
    have hsub : {V : PlaneTree | k ≤ rootLeafHeight V} ⊆ {V | m ≤ rootLeafHeight V} :=
      fun V (hV : k ≤ rootLeafHeight V) => show m ≤ rootLeafHeight V by omega
    have hform := bienayme_real_rootDegree_mem_forall_exists μ (lhDegrees μ) hsub
    rw [bienayme_real_le_rootLeafHeight hc h1, bienayme_real_le_rootLeafHeight hc h1] at hform
    rw [lh_mark_and_le_eq, hform]
    have hb0 : 0 ≤ a - piSeq μ k := sub_nonneg.mpr hka
    have hba : a - piSeq μ k ≤ a := by linarith
    calc ∑' d, (lhDegrees μ).indicator
            (fun d => mass μ d * (a ^ d - (a - piSeq μ k) ^ d)) d
        ≤ ∑' d, (lhDegrees μ).indicator (fun d => (d : ℝ) * mass μ d) d *
            (piSeq μ k * a ^ kappa μ) := by
          refine (summable_indicator_mass_mul (lhDegrees μ) (fun d => sub_nonneg.mpr
              (pow_le_pow_left₀ hb0 hba d)) (fun d => by
                have := pow_nonneg hb0 d; have := pow_le_one₀ ha0 ha1 (n := d); linarith)
              ).tsum_le_tsum (fun d => ?_) ((summable_cB hc _).mul_right _)
          by_cases hd : d ∈ lhDegrees μ
          · rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd]
            have := pow_sub_pow_le_of_le hb0 hba ha1 (d := d) hd
            calc mass μ d * (a ^ d - (a - piSeq μ k) ^ d)
                ≤ mass μ d * (d * (a - (a - piSeq μ k)) * a ^ kappa μ) :=
                  mul_le_mul_of_nonneg_left this (mass_nonneg d)
              _ = d * mass μ d * (piSeq μ k * a ^ kappa μ) := by ring
          · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hd, zero_mul]
      _ = cConst μ * (piSeq μ k * a ^ kappa μ) := by
          rw [tsum_mul_right, ← cBReal, cBReal_lhDegrees hc]
      _ ≤ 1 * (piSeq μ k * a ^ kappa μ) := by gcongr
      _ ≤ (mass μ (kappa μ))⁻¹ * piSeq μ k * piSeq μ (m + 1) := by
          have hg := (g_bounds hc h1 ha0 ha1).1
          rw [← piSeq_succ] at hg
          have h' : a ^ kappa μ ≤ (mass μ (kappa μ))⁻¹ * piSeq μ (m + 1) := by
            rw [le_inv_mul_iff₀ hκ]
            exact hg
          calc 1 * (piSeq μ k * a ^ kappa μ)
              ≤ piSeq μ k * ((mass μ (kappa μ))⁻¹ * piSeq μ (m + 1)) := by
                rw [one_mul]; exact mul_le_mul_of_nonneg_left h' hπk0.le
            _ = (mass μ (kappa μ))⁻¹ * piSeq μ k * piSeq μ (m + 1) := by ring


/-- Lemma `lem:lh_conditional_mark` with `π_k = P(λ_∅(𝒯) ≥ k)` written as a probability. -/
theorem lem_lh_conditional_mark_prob (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m k : ℕ, m ≤ k →
      (bienayme μ).real {T | lhDeclumpedMark μ k T ∧ m ≤ rootLeafHeight T} ≤
        C * (bienayme μ).real {T | k ≤ rootLeafHeight T} *
          (bienayme μ).real {T | m ≤ rootLeafHeight T} := by
  simp only [bienayme_real_le_rootLeafHeight hc h1]
  exact lem_lh_conditional_mark hc h1

end RootDeclumping
end PoissonDeclumping
