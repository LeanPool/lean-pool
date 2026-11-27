/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeChangeOfVariables
public import LeanPool.FunctionSpaces.Rd.Differences.PointwiseMultipliers

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Leibniz rule in `W^m_p`

Let `V` be a finite-dimensional real inner product space with Lebesgue measure and the
orthonormal basis `e_0, …, e_{n-1}` of `Rd.gridBasis`. A **word** of length `k` is a map
`w : Fin k → Fin n`; it stands for the derivative `∂^{e_w} = ∂_{e_{w_0}} ⋯ ∂_{e_{w_{k-1}}}`.

* **Composition** (`Rd.HasWeakLineDeriv.snoc`, `Rd.HasWeakLineDeriv.of_snoc`): if `h = ∂_w f`,
  then `g = ∂^u h` iff `g = ∂^{(u, w)} f`, the last direction acting first.
* **Words to directions** (`Rd.iteratedLineDerivOp_eq_sum_prod_smul`,
  `Rd.hasWeakLineDeriv_of_gridBasis_words`): `∂^v` is multilinear in `v`, so
  `∂^v f = ∑_w ∏_l ⟪v_l, e_{w_l}⟫ ∂^{e_w} f`, and derivatives along all words of length `k` give
  the derivatives along all directions `v ∈ V^k`.
* **The Leibniz rule with a bound** (`Rd.exists_hasWeakLineDeriv_mul_of_tsupport_subset`): if
  `f` has the weak derivatives `g_{k,w} = ∂^{e_w} f` on `O ∩ B` for all words of length `k ≤ m`
  and `χ` is smooth with compact support in `B`, then `χ f` has weak derivatives `G_w` on `O`
  along all words of length `k ≤ m`, with
  `‖G_w‖_{L_p(O)} ≤ C_k(χ) ∑_{k' ≤ k} ∑_{w'} ‖g_{k',w'}‖_{L_p(O ∩ B)}`. The constant is
  `C_k(χ) = 2^k sup_x ∑_{j ≤ k} ‖D^j χ(x)‖` (`Rd.leibnizConst`, finite by
  `Rd.leibnizConst_ne_top`); the proof is the induction `∂_i (χ f) = χ ∂_i f + (∂_i χ) f`.
* **Sums over words** (`Rd.le_sum_range_sum_words`, `Rd.sum_range_sum_words_mono`,
  `Rd.sum_range_sum_words_sum_mul`): elementary bounds for `∑_{k ≤ m} ∑_w a_{k,w}`, and one
  family of choices along all words of length at most `m`
  (`Rd.exists_forall_words_of_forall_le`).
* **Smooth compactly supported multipliers on `W^m_p(V)`**
  (`Rd.MemSobolev.mulLp_of_hasCompactSupport`): `χ F ∈ W^m_p(V)` for `F ∈ W^m_p(V)`, since
  derivatives in `L_p(V)` along all words of length `k ≤ m` give `W^m_p(V)`
  (`Rd.memSobolev_of_forall_gridBasis_words`); the case `m = 1` is `Rd.MemSobolev.mulLp`.
* **The product rule in `L_p(V)`** (`Rd.hasWeakLineDeriv_mulLp`): `∂_w (χ F) = χ ∂_w F + (∂_w χ) F`
  for every smooth bounded `χ` with bounded `∂_w χ`.
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Set
open scoped ENNReal NNReal LineDeriv Distributions

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Composition of weak derivatives -/

section Composition

variable {Ω : Opens V} {f h g : V → ℂ} {k : ℕ} {u : Fin k → V} {w : V}

/-- **Composition of weak derivatives**: if `h = ∂_w f` and `g = ∂^u h` weakly on `Ω`, then
`g = ∂^{(u, w)} f` weakly on `Ω`, where `∂_w` acts first (Mathlib's
`LineDeriv.iteratedLineDerivOp_succ_right`). -/
theorem HasWeakLineDeriv.snoc (h₁ : HasWeakLineDeriv Ω (fun _ : Fin 1 => w) f h)
    (h₂ : HasWeakLineDeriv Ω u h g) : HasWeakLineDeriv Ω (Fin.snoc u w) f g := by
  refine ⟨h₁.1, h₂.2, ?_⟩
  have e1 := h₁.eq
  rw [LineDeriv.iteratedLineDerivOp_one] at e1
  rw [LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last, e1, h₂.eq]

/-- **Weak derivatives of a first derivative**: if `h = ∂_w f` and `g = ∂^{(u, w)} f` weakly on
`Ω`, then `g = ∂^u h` weakly on `Ω`, the converse of `Rd.HasWeakLineDeriv.snoc`. -/
theorem HasWeakLineDeriv.of_snoc (h₁ : HasWeakLineDeriv Ω (fun _ : Fin 1 => w) f h)
    (h₂ : HasWeakLineDeriv Ω (Fin.snoc u w) f g) : HasWeakLineDeriv Ω u h g := by
  refine ⟨h₁.2, h₂.2, ?_⟩
  have e1 := h₁.eq
  rw [LineDeriv.iteratedLineDerivOp_one] at e1
  rw [← e1, ← h₂.eq, LineDeriv.iteratedLineDerivOp_succ_right (Fin.snoc u w), Fin.init_snoc,
    Fin.snoc_last]

end Composition

/-! ### Words and directions -/

section Words

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Iterated derivatives are multilinear in the directions**: if
`v_l = ∑_j c_{l,j} b_j` for `l < k`, then
`∂^v T = ∑_{i : Fin k → ι} (∏_l c_{l, i_l}) ∂_{b_{i_0}} ⋯ ∂_{b_{i_{k-1}}} T`, for every `T` in a
space with additive and homogeneous derivatives, such as distributions. By induction on `k`,
with Mathlib's `LineDeriv.lineDerivOp_left_sum` and the splitting of words by `Fin.consEquiv`. -/
theorem iteratedLineDerivOp_eq_sum_prod_smul {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [LineDeriv V E E] [LineDerivAdd V E E] [LineDerivSMul ℝ V E E] [LineDerivLeftSMul ℝ V E E]
    [Fintype ι] (b : ι → V) {k : ℕ} (c : Fin k → ι → ℝ) (T : E) :
    ∂^{fun l => ∑ j, c l j • b j} T =
      ∑ i : Fin k → ι, (∏ l, c l (i l)) • ∂^{fun l => b (i l)} T := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    have ht : Fin.tail (fun l : Fin (k + 1) => ∑ j, c l j • b j) =
        fun l => ∑ j, c l.succ j • b j := rfl
    rw [ht, ih (fun l => c l.succ), LineDeriv.lineDerivOp_left_sum,
      ← Fintype.sum_equiv (Fin.consEquiv fun _ => ι) _ _ fun _ => rfl, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LineDeriv.lineDerivOp_left_smul, LineDeriv.lineDerivOp_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      LineDeriv.lineDerivOp_smul, smul_smul]
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    rfl

variable {Ω : Opens V} {f : V → ℂ}

/-- The distribution of a finite combination `∑_i c_i g_i` with real `c_i` of locally integrable
functions is `∑_i c_i` times the distributions of the `g_i` (Mathlib's `Distribution.ofFun_add`
and `Distribution.ofFun_smul`). -/
theorem ofFun_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → V → ℂ}
    (hg : ∀ i ∈ s, LocallyIntegrableOn (g i) Ω volume) :
    Distribution.ofFun Ω (∑ i ∈ s, c i • g i) volume ⊤ =
      ∑ i ∈ s, c i • Distribution.ofFun Ω (g i) volume ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Distribution.ofFun_zero]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, LocallyIntegrableOn (g j) Ω volume := fun j hj =>
      hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Distribution.ofFun_add ((hg i (Finset.mem_insert_self i s)).smul _)
        (locallyIntegrableOn_sum_smul s c hs),
      Distribution.ofFun_smul, ih hs]

/-- **Weak derivatives along all directions from the words**: if `g_w = ∂^{e_w} f` weakly on `Ω`
for every word `w` of length `k`, then for all directions `v ∈ V^k`,
`∑_w ∏_l ⟪v_l, e_{w_l}⟫ g_w = ∂^v f` weakly on `Ω`
(`Rd.iteratedLineDerivOp_eq_sum_prod_smul` with `v_l = ∑_j ⟪v_l, e_j⟫ e_j`, Mathlib's
`OrthonormalBasis.sum_repr'`). -/
theorem hasWeakLineDeriv_of_gridBasis_words {k : ℕ} {g : (Fin k → Fin (finrank ℝ V)) → V → ℂ}
    (hf : LocallyIntegrableOn f Ω volume)
    (h : ∀ w, HasWeakLineDeriv Ω (fun l => gridBasis V (w l)) f (g w)) (v : Fin k → V) :
    HasWeakLineDeriv Ω v f
      (fun x => ∑ w, (∏ l, (inner ℝ (v l) (gridBasis V (w l)) : ℂ)) * g w x) := by
  have hv : v = fun l => ∑ j, inner ℝ (v l) (gridBasis V j) • gridBasis V j := funext fun l => by
    simpa only [real_inner_comm] using ((gridBasis V).sum_repr' (v l)).symm
  have hfun : (fun x => ∑ w, (∏ l, (inner ℝ (v l) (gridBasis V (w l)) : ℂ)) * g w x) =
      ∑ w, (∏ l, inner ℝ (v l) (gridBasis V (w l))) • g w := funext fun x => by
    simp [Finset.sum_apply, Complex.real_smul]
  refine ⟨hf, ?_, ?_⟩
  · rw [hfun]
    exact locallyIntegrableOn_sum_smul _ _ fun w _ => (h w).2
  · rw [hfun, ofFun_sum_smul _ _ fun w _ => (h w).2]
    conv_lhs => rw [hv]
    rw [iteratedLineDerivOp_eq_sum_prod_smul]
    exact Finset.sum_congr rfl fun w _ => by rw [(h w).eq]

end Words

/-! ### The Leibniz constant -/

section Constant

/-- The **Leibniz constant** `C_k(χ) = 2^k sup_x ∑_{j ≤ k} ‖D^j χ(x)‖` of a smooth function `χ`: the
weak derivatives of order `k` of `χ f` are bounded by `C_k(χ)` times the derivatives of `f` of order
at most `k` (`Rd.exists_hasWeakLineDeriv_mul_of_tsupport_subset`). -/
noncomputable def leibnizConst (χ : V → ℝ) (k : ℕ) : ℝ≥0∞ :=
  2 ^ k * ⨆ x, ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j χ x‖ₑ

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Leibniz constant of a smooth function with compact support is finite: each derivative
`D^j χ` is continuous with compact support, hence bounded (Mathlib's
`Continuous.bounded_above_of_compact_support`). -/
theorem leibnizConst_ne_top {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hc : HasCompactSupport χ) (k : ℕ) : leibnizConst χ k ≠ ∞ := by
  choose C hC using fun j : ℕ => (hχ.continuous_iteratedFDeriv (m := j)
    (by exact_mod_cast le_top)).bounded_above_of_compact_support (hc.iteratedFDeriv j)
  have hS : (⨆ x, ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j χ x‖ₑ) ≤
      ∑ j ∈ Finset.range (k + 1), ENNReal.ofReal (C j) :=
    iSup_le fun x => Finset.sum_le_sum fun j _ => by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC j x)
  exact ENNReal.mul_ne_top (by simp)
    (ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top) hS)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The values of `χ` are bounded by the Leibniz constant of order `0`. -/
theorem enorm_le_leibnizConst_zero (χ : V → ℝ) (x : V) : ‖χ x‖ₑ ≤ leibnizConst χ 0 := by
  rw [leibnizConst, pow_zero, one_mul]
  refine le_trans ?_ (le_iSup _ x)
  rw [Finset.sum_range_one, ← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The derivatives of a directional derivative**: for a smooth `χ` and `‖v‖ ≤ 1`,
`‖D^j (∂_v χ)(x)‖ ≤ ‖D^{j+1} χ(x)‖` (Mathlib's `norm_iteratedFDeriv_clm_apply_const` and
`norm_iteratedFDeriv_fderiv`). -/
theorem enorm_iteratedFDeriv_fderiv_apply_le {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {v : V} (hv : ‖v‖ ≤ 1) (j : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ χ y v) x‖ₑ ≤ ‖iteratedFDeriv ℝ (j + 1) χ x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := norm_iteratedFDeriv_clm_apply_const (c := v) (x := x) (n := j)
    ((hχ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).contDiffAt)
    (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hv)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The Leibniz constants grow along the induction**: for a smooth `χ` and `‖v‖ ≤ 1`,
`C_k(χ) + C_k(∂_v χ) ≤ C_{k+1}(χ)`, since both suprema are at most
`sup_x ∑_{j ≤ k+1} ‖D^j χ(x)‖` (`Rd.enorm_iteratedFDeriv_fderiv_apply_le`). -/
theorem leibnizConst_add_le {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {v : V}
    (hv : ‖v‖ ≤ 1) (k : ℕ) :
    leibnizConst χ k + leibnizConst (fun y => fderiv ℝ χ y v) k ≤ leibnizConst χ (k + 1) := by
  set S := ⨆ x, ∑ j ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ j χ x‖ₑ
  have h1 : (⨆ x, ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j χ x‖ₑ) ≤ S :=
    iSup_mono fun x => by
      rw [Finset.sum_range_succ _ (k + 1)]
      exact le_self_add
  have h2 : (⨆ x, ∑ j ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ χ y v) x‖ₑ) ≤ S := iSup_mono fun x => by
    rw [Finset.sum_range_succ' _ (k + 1)]
    exact le_add_right (Finset.sum_le_sum fun j _ => enorm_iteratedFDeriv_fderiv_apply_le hχ hv j x)
  calc leibnizConst χ k + leibnizConst (fun y => fderiv ℝ χ y v) k ≤ 2 ^ k * S + 2 ^ k * S :=
        add_le_add (mul_le_mul_right h1 _) (mul_le_mul_right h2 _)
    _ = leibnizConst χ (k + 1) := by rw [leibnizConst, pow_succ]; ring

end Constant

/-! ### The Leibniz rule -/

section Leibniz

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **Words with a fixed last letter**: for nonnegative `a`, the sum over the words `(w, j)` of
length `k + 1` that end with `j` is at most the sum over all words of length `k + 1` (the map
`w ↦ (w, j)` is injective, Mathlib's `Fin.snoc_left_injective`). -/
theorem sum_snoc_le {ι : Type*} [Fintype ι] {k : ℕ} (a : (Fin (k + 1) → ι) → ℝ≥0∞) (j : ι) :
    ∑ w : Fin k → ι, a (Fin.snoc w j) ≤ ∑ w, a w := by
  classical
  rw [← Finset.sum_image fun x _ y _ h => Fin.snoc_left_injective (α := fun _ => ι) j h]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **The sums of the induction step**: the sum over the words of length `k' + 1 ≤ k + 1` that end
with `j` is at most the sum over all words of length at most `k + 1` (`Rd.sum_snoc_le`). -/
theorem sum_range_sum_snoc_le {ι : Type*} [Fintype ι] (a : (k : ℕ) → (Fin k → ι) → ℝ≥0∞) (j : ι)
    (k : ℕ) :
    ∑ k' ∈ Finset.range (k + 1), ∑ w : Fin k' → ι, a (k' + 1) (Fin.snoc w j) ≤
      ∑ k' ∈ Finset.range (k + 2), ∑ w : Fin k' → ι, a k' w := by
  rw [Finset.sum_range_succ' _ (k + 1)]
  exact le_add_right (Finset.sum_le_sum fun k' _ => sum_snoc_le (a (k' + 1)) j)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **One term of a sum over words**: for nonnegative `a` and a word `w` of length `k ≤ m`,
`a_{k,w} ≤ ∑_{k' ≤ m} ∑_{w'} a_{k',w'}`, the sum over all words of length at most `m`. -/
theorem le_sum_range_sum_words {ι : Type*} [Fintype ι] (a : (k : ℕ) → (Fin k → ι) → ℝ≥0∞)
    {k m : ℕ} (hk : k ≤ m) (w : Fin k → ι) :
    a k w ≤ ∑ k' ∈ Finset.range (m + 1), ∑ w' : Fin k' → ι, a k' w' :=
  (Finset.single_le_sum (f := fun w' => a k w') (fun _ _ => zero_le) (Finset.mem_univ w)).trans
    (Finset.single_le_sum (f := fun k' => ∑ w' : Fin k' → ι, a k' w') (fun _ _ => zero_le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **Sums over words of increasing length**: for nonnegative `a` and `k ≤ m`, the sum over the
words of length at most `k` is at most the sum over the words of length at most `m`. -/
theorem sum_range_sum_words_mono {ι : Type*} [Fintype ι] (a : (k : ℕ) → (Fin k → ι) → ℝ≥0∞)
    {k m : ℕ} (hk : k ≤ m) :
    ∑ k' ∈ Finset.range (k + 1), ∑ w' : Fin k' → ι, a k' w' ≤
      ∑ k' ∈ Finset.range (m + 1), ∑ w' : Fin k' → ι, a k' w' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **Exchanging the sums over words and over an index set**: for nonnegative `λ_{i,k}` and
`c_i`, `∑_{k ≤ m} ∑_w ∑_i λ_{i,k} c_i = ∑_i (∑_{k ≤ m} ∑_w λ_{i,k}) c_i`. -/
theorem sum_range_sum_words_sum_mul {ι κ : Type*} [Fintype ι] [Fintype κ] (m : ℕ)
    (lam : ι → ℕ → ℝ≥0∞) (c : ι → ℝ≥0∞) :
    ∑ k ∈ Finset.range (m + 1), ∑ _w : Fin k → κ, ∑ i, lam i k * c i =
      ∑ i, (∑ k ∈ Finset.range (m + 1), ∑ _w : Fin k → κ, lam i k) * c i := by
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.sum_mul]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **A choice along the words of length at most `m`**: if for every word `w` of length `k ≤ m`
some `a` satisfies `P k w a`, then one family `(a_{k,w})`, indexed by all words, satisfies
`P k w a_{k,w}` for every word `w` of length `k ≤ m`. -/
theorem exists_forall_words_of_forall_le {ι α : Type*} [Nonempty α] {m : ℕ}
    {P : (k : ℕ) → (Fin k → ι) → α → Prop} (h : ∀ k ≤ m, ∀ w, ∃ a, P k w a) :
    ∃ G : (k : ℕ) → (Fin k → ι) → α, ∀ k ≤ m, ∀ w, P k w (G k w) := by
  classical
  refine ⟨fun k w => if hk : k ≤ m then (h k hk w).choose else Classical.arbitrary α,
    fun k hk w => ?_⟩
  simp only [hk, ↓reduceDIte]
  exact (h k hk w).choose_spec

omit [MeasurableSpace V] [BorelSpace V] in
/-- The basis directions of a word `(u, j)` are those of `u` followed by `e_j` (Mathlib's
`Fin.comp_snoc`). -/
theorem gridBasis_snoc {k : ℕ} (u : Fin k → Fin (finrank ℝ V)) (j : Fin (finrank ℝ V)) :
    (fun l => gridBasis V (Fin.snoc (α := fun _ => Fin (finrank ℝ V)) u j l)) =
      Fin.snoc (α := fun _ => V) (fun l => gridBasis V (u l)) (gridBasis V j) :=
  Fin.comp_snoc (gridBasis V) u j

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {O B : Opens V}

omit [Fact (1 ≤ p)] in
/-- **The base case of the Leibniz rule**: the derivative of order `0` of `χ f` is `χ f`, with
`‖χ f‖_{L_p(O)} ≤ C_0(χ) ‖g_0‖_{L_p(O ∩ B)}` for `g_0 = f` almost everywhere on `O ∩ B`
(`Rd.eLpNorm_mul_le_of_tsupport_subset`). -/
theorem exists_hasWeakLineDeriv_mul_zero {f : V → ℂ}
    (g : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ)
    (hg : ∀ w : Fin 0 → Fin (finrank ℝ V),
      HasWeakLineDeriv (O ⊓ B) (fun l => gridBasis V (w l)) f (g 0 w))
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχB : tsupport χ ⊆ B) (w : Fin 0 → Fin (finrank ℝ V)) :
    ∃ G : V → ℂ, HasWeakLineDeriv O (fun l => gridBasis V (w l)) (fun x => (χ x : ℂ) * f x) G ∧
      eLpNorm G p (volume.restrict O) ≤ leibnizConst χ 0 *
        ∑ k' ∈ Finset.range 1, ∑ w' : Fin k' → Fin (finrank ℝ V),
          eLpNorm (g k' w') p (volume.restrict (O ⊓ B : Opens V)) := by
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hcB : tsupport (fun x => (χ x : ℂ)) ⊆ B :=
    (tsupport_comp_subset Complex.ofReal_zero χ).trans hχB
  have hf := (hg w).locallyIntegrableOn
  refine ⟨_, hasWeakLineDeriv_fin_zero _ (locallyIntegrableOn_mul_of_tsupport_subset hf hc hcB),
    ?_⟩
  have hC := leibnizConst_ne_top hχ hχc 0
  have hb : ∀ x, ‖χ x‖ ≤ ((leibnizConst χ 0).toNNReal : ℝ) := fun x => by
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_norm, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_toNNReal hC]
    exact enorm_le_leibnizConst_zero χ x
  have hfg : f =ᵐ[volume.restrict (O ⊓ B : Opens V)] g 0 w :=
    (hasWeakLineDeriv_fin_zero (fun l => gridBasis V (w l)) hf).unique (hg w)
  refine (eLpNorm_mul_le_of_tsupport_subset hχ.continuous hχB hb).trans ?_
  rw [ENNReal.coe_toNNReal hC, eLpNorm_congr_ae hfg, Finset.sum_range_one]
  exact mul_le_mul_right (Finset.single_le_sum (f := fun w' => eLpNorm (g 0 w') p _)
    (fun _ _ => zero_le) (Finset.mem_univ w)) _

/-- **The induction step of the Leibniz rule**: if `χ f'` and `(∂_{e_j} χ) f` have the weak
derivatives `G_1`, `G_2` along `u`, where `f' = ∂_{e_j} f` on `O ∩ B`, then `G_1 + G_2` is the weak
derivative of `χ f` along `(u, j)` on `O`, since `∂_{e_j} (χ f) = χ f' + (∂_{e_j} χ) f`
(`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`, `Rd.HasWeakLineDeriv.snoc`). -/
theorem HasWeakLineDeriv.mul_snoc {f f' G₁ G₂ : V → ℂ} {k : ℕ}
    {u : Fin k → Fin (finrank ℝ V)} {j : Fin (finrank ℝ V)}
    (h1 : HasWeakLineDeriv (O ⊓ B) (fun _ : Fin 1 => gridBasis V j) f f') {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχB : tsupport χ ⊆ B)
    (hG₁ : HasWeakLineDeriv O (fun l => gridBasis V (u l)) (fun x => (χ x : ℂ) * f' x) G₁)
    (hG₂ : HasWeakLineDeriv O (fun l => gridBasis V (u l))
      (fun x => (fderiv ℝ χ x (gridBasis V j) : ℂ) * f x) G₂) :
    HasWeakLineDeriv O (fun l => gridBasis V (Fin.snoc (α := fun _ => Fin (finrank ℝ V)) u j l))
      (fun x => (χ x : ℂ) * f x) (G₁ + G₂) := by
  rw [gridBasis_snoc]
  exact (h1.mul_of_tsupport_subset hχ hχB).snoc (hG₁.add hG₂)

/-- **The Leibniz rule with a bound**: let `g_{k,w} = ∂^{e_w} f` weakly on `O ∩ B` for every word
`w` of length `k ≤ m`, and let `χ` be smooth with compact support and `tsupport χ ⊆ B`. Then for
every word `w` of length `k ≤ m` the function `χ f` has a weak derivative `G = ∂^{e_w} (χ f)` on `O`
with `‖G‖_{L_p(O)} ≤ C_k(χ) ∑_{k' ≤ k} ∑_{w'} ‖g_{k',w'}‖_{L_p(O ∩ B)}` (`Rd.leibnizConst`).
By induction on `k`: for `w = (u, j)`,
`∂^{e_w} (χ f) = ∂^{e_u} (χ ∂_{e_j} f) + ∂^{e_u} ((∂_{e_j} χ) f)`, and both terms are of order `k`
(`Rd.HasWeakLineDeriv.mul_snoc`, `Rd.leibnizConst_add_le`). -/
theorem exists_hasWeakLineDeriv_mul_of_tsupport_subset {m : ℕ} {f : V → ℂ}
    (g : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ)
    (hg : ∀ k ≤ m, ∀ w : Fin k → Fin (finrank ℝ V),
      HasWeakLineDeriv (O ⊓ B) (fun l => gridBasis V (w l)) f (g k w))
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχB : tsupport χ ⊆ B) {k : ℕ} (hk : k ≤ m) (w : Fin k → Fin (finrank ℝ V)) :
    ∃ G : V → ℂ, HasWeakLineDeriv O (fun l => gridBasis V (w l)) (fun x => (χ x : ℂ) * f x) G ∧
      eLpNorm G p (volume.restrict O) ≤ leibnizConst χ k *
        ∑ k' ∈ Finset.range (k + 1), ∑ w' : Fin k' → Fin (finrank ℝ V),
          eLpNorm (g k' w') p (volume.restrict (O ⊓ B : Opens V)) := by
  induction k generalizing m f g χ with
  | zero => exact exists_hasWeakLineDeriv_mul_zero g (hg 0 (Nat.zero_le m)) hχ hχc hχB w
  | succ k ih =>
    obtain ⟨u, j, rfl⟩ : ∃ u j, w = Fin.snoc (α := fun _ => Fin (finrank ℝ V)) u j :=
      ⟨Fin.init w, w (Fin.last k), (Fin.snoc_init_self w).symm⟩
    have h1 : HasWeakLineDeriv (O ⊓ B) (fun _ : Fin 1 => gridBasis V j) f (g 1 fun _ => j) :=
      hg 1 (by omega) fun _ => j
    have hg' : ∀ k' ≤ m - 1, ∀ w' : Fin k' → Fin (finrank ℝ V),
        HasWeakLineDeriv (O ⊓ B) (fun l => gridBasis V (w' l)) (g 1 fun _ => j)
          (g (k' + 1) (Fin.snoc w' j)) := fun k' hk' w' => h1.of_snoc (by
      rw [← gridBasis_snoc]
      exact hg (k' + 1) (by omega) (Fin.snoc w' j))
    have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => fderiv ℝ χ x (gridBasis V j) :=
      (hχ.fderiv_right (by simp)).clm_apply contDiff_const
    obtain ⟨G₁, hG₁, hb₁⟩ := ih (m := m - 1) (fun k' w' => g (k' + 1) (Fin.snoc w' j)) hg' hχ
      hχc hχB (by omega) u
    obtain ⟨G₂, hG₂, hb₂⟩ := ih (m := m) g hg hχ' (hχc.fderiv_apply (𝕜 := ℝ) (gridBasis V j))
      ((tsupport_fderiv_apply_subset ℝ _).trans hχB) (by omega) u
    refine ⟨G₁ + G₂, h1.mul_snoc hχ hχB hG₁ hG₂, ?_⟩
    set N := ∑ k' ∈ Finset.range (k + 2), ∑ w' : Fin k' → Fin (finrank ℝ V),
      eLpNorm (g k' w') p (volume.restrict (O ⊓ B : Opens V))
    have hN₁ := sum_range_sum_snoc_le
      (fun k' w' => eLpNorm (g k' w') p (volume.restrict (O ⊓ B : Opens V))) j k
    have hN₂ : ∑ k' ∈ Finset.range (k + 1), ∑ w' : Fin k' → Fin (finrank ℝ V),
        eLpNorm (g k' w') p (volume.restrict (O ⊓ B : Opens V)) ≤ N := by
      simp only [N, Finset.sum_range_succ _ (k + 1)]
      exact le_self_add
    have hv : ‖gridBasis V j‖ ≤ 1 := ((gridBasis V).orthonormal.1 j).le
    calc eLpNorm (G₁ + G₂) p (volume.restrict O)
        ≤ eLpNorm G₁ p (volume.restrict O) + eLpNorm G₂ p (volume.restrict O) :=
          eLpNorm_add_le Fact.out
      _ ≤ leibnizConst χ k * N + leibnizConst (fun x => fderiv ℝ χ x (gridBasis V j)) k * N :=
          add_le_add (hb₁.trans (mul_le_mul_right hN₁ _)) (hb₂.trans (mul_le_mul_right hN₂ _))
      _ ≤ leibnizConst χ (k + 1) * N := by
          rw [← add_mul]
          gcongr
          exact leibnizConst_add_le hχ hv k

end Leibniz

/-! ### Multipliers on `W^m_p(V)` -/

section Multipliers

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Leibniz rule on `V`**: for `F ∈ W^m_p(V)` and a smooth `χ` with compact support, `χ F`
has a weak derivative `G ∈ L_p(V)` along every word of length `k ≤ m`
(`Rd.exists_hasWeakLineDeriv_mul_of_tsupport_subset` with `O = B = V`; the bound is finite since the
derivatives of `F` lie in `L_p(V)`). -/
theorem MemSobolev.exists_hasWeakLineDeriv_mul {m : ℕ} {F : Lp ℂ p (volume : Measure V)}
    (hF : MemSobolev m F) {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hcs : HasCompactSupport χ) {k : ℕ} (hk : k ≤ m) (w : Fin k → Fin (finrank ℝ V)) :
    ∃ G : V → ℂ, MemLp G p volume ∧
      HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) (fun x => (χ x : ℂ) * F x) G := by
  have htop : (⊤ ⊓ ⊤ : Opens V) = ⊤ := inf_idem _
  obtain ⟨g, hg⟩ := exists_forall_words_of_forall_le (m := m)
    (P := fun k w g => MemLp g p volume ∧ HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) F g)
    fun k hk w => (hF.2 k hk fun l => gridBasis V (w l)).imp fun g hg =>
      ⟨volume_restrict_top (V := V) ▸ hg.1, hg.2⟩
  obtain ⟨G, hG, hGb⟩ := exists_hasWeakLineDeriv_mul_of_tsupport_subset (p := p) (O := ⊤) (B := ⊤)
    g (fun k hk w => htop ▸ (hg k hk w).2) hχ hcs (subset_univ _) hk w
  have hfin : eLpNorm G p (volume.restrict (⊤ : Opens V)) < ∞ := by
    refine hGb.trans_lt (ENNReal.mul_lt_top (leibnizConst_ne_top hχ hcs k).lt_top ?_)
    refine ENNReal.sum_lt_top.2 fun k' hk' => ENNReal.sum_lt_top.2 fun w' _ => ?_
    rw [htop, volume_restrict_top]
    exact (hg k' (by have := Finset.mem_range.1 hk'; omega) w').1.eLpNorm_lt_top
  rw [volume_restrict_top] at hfin
  exact ⟨G, memLp_iff.2 hfin, hG⟩

/-- **`W^m_p(V)` from the derivatives along words**: a function `F ∈ L_p(V)`, `1 ≤ p`, with a weak
derivative `G_w ∈ L_p(V)` on `V` along every word `w` of length `k ≤ m` lies in `W^m_p(V)`; the
derivative along `v ∈ V^k` is `∑_w ∏_l ⟪v_l, e_{w_l}⟫ G_w`
(`Rd.hasWeakLineDeriv_of_gridBasis_words`). For `m = 1` this is
`Rd.memSobolev_one_of_forall_gridBasis`. -/
theorem memSobolev_of_forall_gridBasis_words {m : ℕ} {F : Lp ℂ p (volume : Measure V)}
    (h : ∀ k ≤ m, ∀ w : Fin k → Fin (finrank ℝ V), ∃ G : V → ℂ, MemLp G p volume ∧
      HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) F G) : MemSobolev m F := by
  refine ⟨by simpa using Lp.memLp F, fun k hk v => ?_⟩
  choose G hG hGd using h k hk
  have hD : MemLp (fun x => ∑ w, (∏ l, (inner ℝ (v l) (gridBasis V (w l)) : ℂ)) * G w x) p
      (volume.restrict ((⊤ : Opens V) : Set V)) := by
    rw [volume_restrict_top]
    have h' := memLp_finsetSum' Finset.univ fun w _ =>
      (hG w).const_mul (∏ l, (inner ℝ (v l) (gridBasis V (w l)) : ℂ))
    convert h' using 1
    funext x
    simp [Finset.sum_apply]
  exact ⟨_, hD, hasWeakLineDeriv_of_gridBasis_words (locallyIntegrableOn_top_Lp _) hGd v⟩

/-- **Smooth compactly supported multipliers keep `W^m_p(V)`**: if `F ∈ W^m_p(V)` and `χ` is a
smooth real function with compact support, then `χ F ∈ W^m_p(V)`. Here `hc` and `hC` are the
continuity and the bound `|χ| ≤ C` with which the product `Rd.mulLp` in `L_p` is formed; both
follow from smoothness and compact support. The derivatives along words come from the Leibniz rule
(`Rd.MemSobolev.exists_hasWeakLineDeriv_mul`), those along all directions from the words
(`Rd.memSobolev_of_forall_gridBasis_words`). -/
theorem MemSobolev.mulLp_of_hasCompactSupport {m : ℕ} {F : Lp ℂ p (volume : Measure V)}
    (hF : MemSobolev m F) {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hcs : HasCompactSupport χ) {C : ℝ} (hc : Continuous fun x => (χ x : ℂ))
    (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) : MemSobolev m (mulLp hc hC F) := by
  have hae : (fun x => (χ x : ℂ) * F x) =ᵐ[volume.restrict ((⊤ : Opens V) : Set V)]
      (mulLp hc hC F : V → ℂ) := by
    rw [volume_restrict_top]
    exact (mulLp_apply_ae hc hC F).symm
  refine memSobolev_of_forall_gridBasis_words fun k hk w => ?_
  obtain ⟨G, hG, hGd⟩ := hF.exists_hasWeakLineDeriv_mul hχ hcs hk w
  exact ⟨G, hG, hGd.congr_ae hae EventuallyEq.rfl⟩

omit [Fact (1 ≤ p)] in
/-- **The product rule in `L_p(V)`**: if `G = ∂_w F` weakly on `V` and `χ` is a smooth real
function, bounded with its derivative `∂_w χ` (bounds `C`, `C'`), then `χ G + (∂_w χ) F` is the weak
derivative `∂_w (χ F)` on `V`, with the products `Rd.mulLp` in `L_p(V)`
(`Rd.HasWeakLineDeriv.mul_contDiff`). -/
theorem hasWeakLineDeriv_mulLp {w : V} {F G : Lp ℂ p (volume : Measure V)}
    (h : HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) F G) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) {C C' : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C)
    (hc' : Continuous fun x => (fderiv ℝ χ x w : ℂ)) (hC' : ∀ x, ‖(fderiv ℝ χ x w : ℂ)‖ ≤ C') :
    HasWeakLineDeriv ⊤ (fun _ : Fin 1 => w) (mulLp hc hC F)
      ((mulLp hc hC G + mulLp hc' hC' F : Lp ℂ p (volume : Measure V)) : V → ℂ) := by
  refine (h.mul_contDiff hχ).congr_ae ?_ ?_ <;> rw [volume_restrict_top]
  · exact (mulLp_apply_ae hc hC F).symm
  · filter_upwards [Lp.coeFn_add (mulLp hc hC G) (mulLp hc' hC' F), mulLp_apply_ae hc hC G,
      mulLp_apply_ae hc' hC' F] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]

/-- **Smooth compactly supported multipliers keep `W^1_p(V)`**: if `F ∈ W^1_p(V)` and `χ` is a
smooth real function with compact support, then `χ F ∈ W^1_p(V)`, the case `m = 1` of
`Rd.MemSobolev.mulLp_of_hasCompactSupport`. -/
theorem MemSobolev.mulLp {F : Lp ℂ p (volume : Measure V)} (hF : MemSobolev 1 F)
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcs : HasCompactSupport χ) {C : ℝ}
    (hc : Continuous fun x => (χ x : ℂ)) (hC : ∀ x, ‖(χ x : ℂ)‖ ≤ C) :
    MemSobolev 1 (mulLp hc hC F) :=
  hF.mulLp_of_hasCompactSupport hχ hcs hc hC

end Multipliers

end Rd
