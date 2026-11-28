/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Instances.NTerm
public import LeanPool.FunctionSpaces.ApproximationSpaces.Dyadic
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Rearrangement
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Best `n`-term approximation from a Hilbert basis

Let `H` be a complex Hilbert space with a Hilbert basis `(e_i)_{i ∈ ι}` and let
`γ_i(f) = |⟨e_i, f⟩|` be the moduli of the coefficients of `f ∈ H`. The **dictionary** of the
basis is the set of the multiples `c e_i`, `c ∈ ℂ` (`HilbertBasis.coeffDictionary`), so the
approximants of `n`-term approximation (`ApproximationScheme.nTerm`) are the combinations
`∑_{i ∈ Λ} c_i e_i` with `#Λ ≤ n`. By Parseval's identity (`lp.enorm_sq_eq_tsum`) the error is
the tail of the coefficients outside the best set `Λ`:

`E_n(f)² = inf_{#Λ ≤ n} ∑_{i ∉ Λ} γ_i(f)²`   (`HilbertBasis.approxError_nTerm_sq_eq`).

With the decreasing rearrangement `γ*_k` of the coefficients (`TauCeti.decreasingRearrangement`,
`ApproximationSpaces.Sequences.Rearrangement`),
`∑_{k ≥ N} (γ*_k)² ≤ E_N(f)² ≤ ∑_k min(γ*_k, γ*_N)²`.
For `0 < τ ≤ 2` and `θ = 1/τ - 1/2` this gives the tail bound with constant `1`

`E_n(f) ≤ (n + 1)^(-θ) ‖(γ_i(f))_i‖_{ℓ_τ}`   for every `n ≥ 0`
(`HilbertBasis.approxError_nTerm_le`; Dung–Temlyakov–Ullrich, *Hyperbolic Cross Approximation*,
Lemma 7.8 in the numbering of arXiv:1601.03978v3), and, for `τ < 2`, through the dyadic blocks
`2^m (γ*_{2^(m+1)})² ≤ E_{2^m}(f)² ≤ 2 ∑_{l ≥ m} 2^l (γ*_{2^l})²`, the theorem of Stechkin and
DeVore:

`f ∈ A^θ_τ(nTerm)  ↔  ∑_i |⟨e_i, f⟩|^τ < ∞`   (`HilbertBasis.memApprox_nTerm_iff`),

with the two-sided bound `∑_i γ_i(f)^τ ≤ 4 ‖f‖^τ_{A^θ_τ}` and
`‖f‖_{A^θ_τ} ≤ C_τ ‖(γ_i(f))_i‖_{ℓ_τ}` for the dyadic quasi-norm
(`HilbertBasis.tsum_repr_rpow_le`, `HilbertBasis.approxNormDyadic_nTerm_le`,
`HilbertBasis.stechkinConst`). The case `τ = 1` is Stechkin's theorem (Dokl. Akad. Nauk SSSR
102, 1955). For general `τ` the sequence form goes back to Pietsch (*Approximation spaces*,
J. Approx. Theory 32, 1981, Example 1 in §3.2), and DeVore (*Nonlinear approximation*, Acta
Numer. 7, 1998, Theorem 4) proves it by interpolation; the proof here works with the dyadic
blocks directly. The range `τ < 1`, where `A^θ_τ` is only quasi-normed, is included.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal InnerProductSpace

/-- `min(x², y²) ≤ x^τ y^(2-τ)` in `[0, ∞]` for `0 ≤ τ ≤ 2`. -/
private theorem min_sq_le_rpow_mul_rpow (x y : ℝ≥0∞) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2) :
    min (x ^ 2) (y ^ 2) ≤ x ^ τ * y ^ (2 - τ) := by
  have hsplit (z : ℝ≥0∞) : z ^ 2 = z ^ τ * z ^ (2 - τ) := by
    rw [← ENNReal.rpow_add_of_nonneg (x := z) τ (2 - τ) hτ0 (sub_nonneg.2 hτ2), add_sub_cancel,
      ENNReal.rpow_two]
  rcases le_total x y with h | h
  · calc min (x ^ 2) (y ^ 2) ≤ x ^ 2 := min_le_left _ _
      _ = x ^ τ * x ^ (2 - τ) := hsplit x
      _ ≤ x ^ τ * y ^ (2 - τ) := by gcongr
  · calc min (x ^ 2) (y ^ 2) ≤ y ^ 2 := min_le_right _ _
      _ = y ^ τ * y ^ (2 - τ) := hsplit y
      _ ≤ x ^ τ * y ^ (2 - τ) := by gcongr

namespace HilbertBasis

open ApproximationScheme ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (b : HilbertBasis ι ℂ H)

/-! ### The dictionary and the error -/

/-- The **coefficient dictionary** of a Hilbert basis `(e_i)`: the multiples `c e_i`, `c ∈ ℂ`.
The scheme `nTerm` takes real linear spans, so complex multiples are needed for its approximants
to be all complex combinations of `n` basis vectors. -/
noncomputable def coeffDictionary : Set H := Set.range fun p : ι × ℂ => p.2 • b p.1

/-- Every complex multiple of a basis vector lies in the coefficient dictionary. -/
theorem smul_mem_coeffDictionary (c : ℂ) (i : ι) : c • b i ∈ b.coeffDictionary :=
  ⟨(i, c), rfl⟩

/-- The coefficients of a finite combination: `⟨e_i, ∑_{j ∈ Λ} c_j e_j⟩ = c_i` for `i ∈ Λ` and
`0` otherwise, by orthonormality. -/
theorem repr_sum_smul [DecidableEq ι] (Λ : Finset ι) (c : ι → ℂ) (i : ι) :
    b.repr (∑ j ∈ Λ, c j • b j) i = if i ∈ Λ then c i else 0 := by
  rw [b.repr_apply_apply, inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal i, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq Λ i c

/-- **The coefficients form a null family**: `|⟨e_i, f⟩| → 0` along the cofinite filter, since
`∑_i |⟨e_i, f⟩|² < ∞`. -/
theorem tendsto_norm_repr (f : H) : Tendsto (fun i => ‖b.repr f i‖) cofinite (𝓝 0) := by
  have hsq : Tendsto (fun i => ‖b.repr f i‖ ^ 2) cofinite (𝓝 0) := by
    simpa [Real.rpow_two] using ((lp.memℓp (b.repr f)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).tendsto_cofinite_zero
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- Every coefficient is at most the norm: `γ*_n ≤ ‖f‖` for the rearranged moduli
`γ_i = |⟨e_i, f⟩|`, since `|⟨e_i, f⟩| ≤ ‖f‖`. -/
theorem decreasingRearrangement_norm_repr_le (f : H) (n : ℕ) :
    TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) n ≤ ‖f‖ :=
  TauCeti.decreasingRearrangement_le_of_card_le (norm_nonneg f) (s := ∅) (Nat.zero_le n) fun i _ =>
    (lp.norm_apply_le_norm (by norm_num) (b.repr f) i).trans_eq (b.repr.norm_map f)

/-- **Upper bound for the error**: for every set `Λ` of at most `n` indices,
`E_n(f)² ≤ ∑_{i ∉ Λ} |⟨e_i, f⟩|²`, since `∑_{i ∈ Λ} ⟨e_i, f⟩ e_i` is an approximant and
Parseval's identity computes the distance to it. -/
theorem approxError_nTerm_sq_le [DecidableEq ι] {n : ℕ} {Λ : Finset ι} (hΛ : Λ.card ≤ n)
    (f : H) : (nTerm b.coeffDictionary).approxError f n ^ 2 ≤
      ∑' i, if i ∈ Λ then 0 else ‖b.repr f i‖ₑ ^ 2 := by
  classical
  have ha : (∑ j ∈ Λ, b.repr f j • b j) ∈ nTerm b.coeffDictionary n := by
    refine ⟨Λ.image fun j => b.repr f j • b j, ?_, card_image_le.trans hΛ, ?_⟩
    · intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      exact b.smul_mem_coeffDictionary _ j
    · exact Submodule.sum_mem _ fun j hj =>
        Submodule.subset_span (mem_coe.2 (mem_image_of_mem _ hj))
  calc (nTerm b.coeffDictionary).approxError f n ^ 2
      ≤ ‖f - ∑ j ∈ Λ, b.repr f j • b j‖ₑ ^ 2 := by
        gcongr; exact approxError_le_of_mem ha f
    _ = ∑' i, ‖b.repr (f - ∑ j ∈ Λ, b.repr f j • b j) i‖ₑ ^ 2 := by
        rw [← b.repr.eNorm_map, lp.enorm_sq_eq_tsum]
    _ = _ := by
        congr 1; funext i
        rw [b.repr_apply_apply, inner_sub_right, ← b.repr_apply_apply, ← b.repr_apply_apply,
          repr_sum_smul]
        split_ifs <;> simp

/-- **Lower bound for the error**: every `n`-term approximant `a` has a set `Λ` of at most `n`
indices with `∑_{i ∉ Λ} |⟨e_i, f⟩|² ≤ ‖f - a‖²`. The coefficients of `a` vanish off the indices
`Λ` of the dictionary elements that `a` combines. -/
theorem exists_tsum_ite_le_enorm_sub_sq [DecidableEq ι] {n : ℕ} {a : H}
    (ha : a ∈ nTerm b.coeffDictionary n) (f : H) :
    ∃ Λ : Finset ι, Λ.card ≤ n ∧
      (∑' i, if i ∈ Λ then 0 else ‖b.repr f i‖ₑ ^ 2) ≤ ‖f - a‖ₑ ^ 2 := by
  classical
  obtain ⟨S, hSD, hS, haS⟩ := ha
  choose p hp using fun x : S => hSD (mem_coe.2 x.2)
  refine ⟨S.attach.image fun x => (p x).1, card_image_le.trans (card_attach.le.trans hS), ?_⟩
  set Λ := S.attach.image fun x => (p x).1
  have hzero : ∀ i ∉ Λ, ⟪b i, a⟫_ℂ = 0 := by
    intro i hi
    induction haS using Submodule.span_induction with
    | mem x hx =>
      have hx' : (p ⟨x, mem_coe.1 hx⟩).2 • b (p ⟨x, mem_coe.1 hx⟩).1 = x := hp _
      have hne : i ≠ (p ⟨x, mem_coe.1 hx⟩).1 := fun h =>
        hi (by rw [h]; exact mem_image.2 ⟨⟨x, mem_coe.1 hx⟩, mem_attach _ _, rfl⟩)
      rw [← hx', inner_smul_right, b.orthonormal.inner_eq_zero hne, mul_zero]
    | zero => exact inner_zero_right _
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul t x _ hx => rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, hx, mul_zero]
  calc (∑' i, if i ∈ Λ then 0 else ‖b.repr f i‖ₑ ^ 2) ≤ ∑' i, ‖b.repr (f - a) i‖ₑ ^ 2 := by
        refine tsum_le_tsum fun i => ?_
        split_ifs with hi
        · exact zero_le
        · rw [b.repr_apply_apply, b.repr_apply_apply, inner_sub_right, hzero i hi, sub_zero]
    _ = ‖f - a‖ₑ ^ 2 := by rw [← lp.enorm_sq_eq_tsum, b.repr.eNorm_map]

/-- **The error of best `n`-term approximation from a Hilbert basis**:
`E_n(f)² = inf_{#Λ ≤ n} ∑_{i ∉ Λ} |⟨e_i, f⟩|²`, the smallest tail of the squared coefficients
outside `n` indices (DeVore, *Nonlinear approximation*, 1998, §2). -/
theorem approxError_nTerm_sq_eq [DecidableEq ι] (n : ℕ) (f : H) :
    (nTerm b.coeffDictionary).approxError f n ^ 2 =
      ⨅ (Λ : Finset ι) (_ : Λ.card ≤ n), ∑' i, if i ∈ Λ then 0 else ‖b.repr f i‖ₑ ^ 2 := by
  refine le_antisymm (le_iInf₂ fun Λ hΛ => b.approxError_nTerm_sq_le hΛ f) ?_
  refine le_approxError_sq_iff.2 fun a ha => ?_
  obtain ⟨Λ, hΛ, h⟩ := b.exists_tsum_ite_le_enorm_sub_sq ha f
  exact (iInf₂_le Λ hΛ).trans h

/-! ### Tail bounds by the rearranged coefficients -/

/-- **Upper tail bound**: `E_N(f)² ≤ ∑_k min((γ*_k)², (γ*_N)²)` for the decreasing
rearrangement `γ*` of `γ_i = |⟨e_i, f⟩|`. The at most `N` indices with `γ_i > γ*_N` form an
admissible set, and the remaining coefficients are bounded by `tsum_ite_rpow_le_tsum_min`. -/
theorem approxError_nTerm_sq_le_tsum_min (N : ℕ) (f : H) :
    (nTerm b.coeffDictionary).approxError f N ^ 2 ≤
      ∑' k, min (ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) k) ^ 2)
        (ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) N) ^ 2) := by
  classical
  have hr := b.tendsto_norm_repr f
  have hfin := TauCeti.finite_setOf_decreasingRearrangement_lt hr.bddAbove_range_of_cofinite N
  have hcard : hfin.toFinset.card ≤ N :=
    TauCeti.card_le_of_forall_decreasingRearrangement_lt hr.bddAbove_range_of_cofinite fun i hi =>
      hfin.mem_toFinset.1 hi
  refine (b.approxError_nTerm_sq_le hcard f).trans ?_
  have h := tsum_ite_rpow_le_tsum_min (fun i => norm_nonneg (b.repr f i)) hr two_pos N
  simp only [ENNReal.rpow_two, ofReal_norm] at h
  refine le_trans (le_of_eq ?_) h
  congr 1; funext i
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- **Lower tail bound**: `∑_k (γ*_{k+N})² ≤ E_N(f)²`. Removing at most `N` coefficients leaves at
least the rearranged tail (`tsum_rpow_decreasingRearrangement_add_le`). -/
theorem tsum_decreasingRearrangement_add_sq_le (N : ℕ) (f : H) :
    ∑' k, ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) (k + N)) ^ 2 ≤
      (nTerm b.coeffDictionary).approxError f N ^ 2 := by
  classical
  rw [b.approxError_nTerm_sq_eq]
  refine le_iInf₂ fun Λ hΛ => ?_
  have h := tsum_rpow_decreasingRearrangement_add_le (fun i => norm_nonneg (b.repr f i))
    (b.tendsto_norm_repr f) two_pos hΛ
  simpa only [ENNReal.rpow_two, ofReal_norm] using h

/-- **Dyadic upper bound**: `E_{2^m}(f)² ≤ 2 ∑_{l ≥ 0} 2^(m+l) (γ*_{2^(m+l)})²`, the upper tail
bound condensed (`ENNReal.tsum_min_le_dyadic`). -/
theorem approxError_nTerm_two_pow_sq_le (m : ℕ) (f : H) :
    (nTerm b.coeffDictionary).approxError f (2 ^ m) ^ 2 ≤ 2 * ∑' l, 2 ^ (m + l) *
      ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) (2 ^ (m + l))) ^ 2 :=
  (b.approxError_nTerm_sq_le_tsum_min (2 ^ m) f).trans
    (ENNReal.tsum_min_le_dyadic (fun _ _ h => by
      dsimp only; gcongr; exact TauCeti.antitone_decreasingRearrangement h) m)

/-- **Dyadic lower bound**: `2^m (γ*_{2^(m+1)})² ≤ E_{2^m}(f)²`, from the lower tail bound, since
the `2^m` terms `γ*_{k+2^m}`, `k < 2^m`, are at least `γ*_{2^(m+1)}`. -/
theorem two_pow_mul_decreasingRearrangement_sq_le (m : ℕ) (f : H) :
    2 ^ m * ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) (2 ^ (m + 1)))
      ^ 2 ≤
      (nTerm b.coeffDictionary).approxError f (2 ^ m) ^ 2 := by
  set c := TauCeti.decreasingRearrangement fun i => ‖b.repr f i‖
  refine le_trans ?_ (b.tsum_decreasingRearrangement_add_sq_le (2 ^ m) f)
  calc (2 : ℝ≥0∞) ^ m * ENNReal.ofReal (c (2 ^ (m + 1))) ^ 2
      = ∑ _k ∈ range (2 ^ m), ENNReal.ofReal (c (2 ^ (m + 1))) ^ 2 := by
        rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ∑ k ∈ range (2 ^ m), ENNReal.ofReal (c (k + 2 ^ m)) ^ 2 := by
        gcongr with k hk
        refine TauCeti.antitone_decreasingRearrangement ?_
        have hk' := mem_range.1 hk
        rw [pow_succ]
        omega
    _ ≤ _ := sum_le_tsum _

/-- `E_n(f)² ≤ (γ*_n)^(2-τ) ∑_i γ_i^τ` for `0 < τ ≤ 2`: each term of the upper tail bound is
`min((γ*_k)², (γ*_n)²) ≤ (γ*_k)^τ (γ*_n)^(2-τ)`, and `∑_k (γ*_k)^τ = ∑_i γ_i^τ`. -/
private theorem approxError_nTerm_sq_le_mul {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) (n : ℕ)
    (f : H) : (nTerm b.coeffDictionary).approxError f n ^ 2 ≤
      (∑' i, ‖b.repr f i‖ₑ ^ τ) *
        ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) n) ^ (2 - τ) := by
  set c := TauCeti.decreasingRearrangement fun i => ‖b.repr f i‖
  have hS : ∑' i, ‖b.repr f i‖ₑ ^ τ = ∑' k, ENNReal.ofReal (c k) ^ τ := by
    rw [tsum_ofReal_rpow_decreasingRearrangement (fun i => norm_nonneg (b.repr f i))
      (b.tendsto_norm_repr f) hτ0]
    simp only [ofReal_norm]
  refine (b.approxError_nTerm_sq_le_tsum_min n f).trans ?_
  rw [hS, ← ENNReal.tsum_mul_right]
  exact tsum_le_tsum fun k => min_sq_le_rpow_mul_rpow _ _ hτ0.le hτ2

/-- **The tail bound with constant `1`**: for `0 < τ ≤ 2`, `θ = 1/τ - 1/2` and every `n ≥ 0`,
`E_n(f) ≤ (n + 1)^(-θ) (∑_i |⟨e_i, f⟩|^τ)^(1/τ)`. Since `θ ≥ 0`, it gives
`E_n(f) ≤ n^(-θ) (∑_i |⟨e_i, f⟩|^τ)^(1/τ)` for `n ≥ 1`, and `‖f‖ ≤ (∑_i |⟨e_i, f⟩|^τ)^(1/τ)` at
`n = 0`. The error `E_n(f)` is the tail of the coefficients from the `(n + 1)`-th largest one
on, so this is Dung–Temlyakov–Ullrich, *Hyperbolic Cross Approximation*, Lemma 7.8 (numbering of
arXiv:1601.03978v3), with `m = n + 1`. With `S = ∑_i γ_i^τ`, the weak-type bound
`(n + 1) (γ*_n)^τ ≤ S` turns `E_n(f)² ≤ S (γ*_n)^(2-τ)` into
`E_n(f)² ≤ (n + 1)^(-2θ) S^(2/τ)`. -/
theorem approxError_nTerm_le {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) (n : ℕ) (f : H) :
    (nTerm b.coeffDictionary).approxError f n ≤
      ((n + 1 : ℕ) : ℝ≥0∞) ^ (-(1 / τ - 1 / 2)) * (∑' i, ‖b.repr f i‖ₑ ^ τ) ^ (1 / τ) := by
  set S := ∑' i, ‖b.repr f i‖ₑ ^ τ
  set C := ENNReal.ofReal (TauCeti.decreasingRearrangement (fun i => ‖b.repr f i‖) n)
  have hτ : τ ≠ 0 := hτ0.ne'
  have ha : 0 ≤ (2 - τ) / τ := div_nonneg (by linarith) hτ0.le
  have hn0 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hweak : C ^ τ ≤ S * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (natCast_ne_top (n + 1))), mul_comm]
    have h := succ_mul_rpow_decreasingRearrangement_le (fun i => norm_nonneg (b.repr f i))
      (b.tendsto_norm_repr f) hτ0 n
    simpa only [ofReal_norm] using h
  have hC : C ^ (2 - τ) ≤ S ^ ((2 - τ) / τ) * ((n + 1 : ℕ) : ℝ≥0∞) ^ (-((2 - τ) / τ)) := by
    calc C ^ (2 - τ) = (C ^ τ) ^ ((2 - τ) / τ) := by
          rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hτ]
      _ ≤ (S * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ^ ((2 - τ) / τ) := by gcongr
      _ = S ^ ((2 - τ) / τ) * ((n + 1 : ℕ) : ℝ≥0∞) ^ (-((2 - τ) / τ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.inv_rpow, ENNReal.rpow_neg]
  have e1 : 1 / τ * ((2 : ℕ) : ℝ) = 1 + (2 - τ) / τ := by push_cast; field_simp; ring
  have e2 : -(1 / τ - 1 / 2) * ((2 : ℕ) : ℝ) = -((2 - τ) / τ) := by push_cast; field_simp
  have hsq : (nTerm b.coeffDictionary).approxError f n ^ 2 ≤
      (((n + 1 : ℕ) : ℝ≥0∞) ^ (-(1 / τ - 1 / 2)) * S ^ (1 / τ)) ^ 2 := by
    calc (nTerm b.coeffDictionary).approxError f n ^ 2 ≤ S * C ^ (2 - τ) :=
          b.approxError_nTerm_sq_le_mul hτ0 hτ2 n f
      _ ≤ S * (S ^ ((2 - τ) / τ) * ((n + 1 : ℕ) : ℝ≥0∞) ^ (-((2 - τ) / τ))) := by gcongr
      _ = (((n + 1 : ℕ) : ℝ≥0∞) ^ (-(1 / τ - 1 / 2)) * S ^ (1 / τ)) ^ 2 := by
          rw [mul_pow, ← ENNReal.rpow_natCast (((n + 1 : ℕ) : ℝ≥0∞) ^ _),
            ← ENNReal.rpow_natCast (S ^ _), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, e1, e2,
            ENNReal.rpow_add_of_nonneg 1 ((2 - τ) / τ) zero_le_one ha, ENNReal.rpow_one]
          ring
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at hsq
  exact (ENNReal.rpow_le_rpow_iff two_pos).1 hsq

/-! ### The theorem of Stechkin and DeVore -/

/-- The constant `C_τ = 1 + (2 · 2^(τ/2) (1 - 2^(-(1 - τ/2)))⁻¹)^(1/τ)` of the upper bound
`‖f‖_{A^θ_τ} ≤ C_τ ‖(⟨e_i, f⟩)_i‖_{ℓ_τ}` (`HilbertBasis.approxNormDyadic_nTerm_le`). -/
noncomputable def stechkinConst (τ : ℝ) : ℝ≥0∞ :=
  1 + (2 ^ (τ / 2) * (1 - 2 ^ (-(1 - τ / 2)))⁻¹ * 2) ^ (1 / τ)

/-- The constant `C_τ` is finite for `0 < τ < 2`. -/
theorem stechkinConst_ne_top {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) : stechkinConst τ ≠ ∞ := by
  refine ENNReal.add_ne_top.2 ⟨one_ne_top, ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_⟩
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (two_rpow_ne_top _)
    (one_sub_two_rpow_neg_inv_ne_top (by linarith))) (by norm_num)

/-- **`ℓ_τ ⊆ ℓ_2` for the coefficients**: `‖f‖ ≤ (∑_i |⟨e_i, f⟩|^τ)^(1/τ)` for `0 < τ ≤ 2`, by
Parseval's identity and the decrease of the `ℓ_p` sums in `p` (`ENNReal.rpow_tsum_rpow_le`). -/
theorem enorm_le_tsum_repr_rpow {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) (f : H) :
    ‖f‖ₑ ≤ (∑' i, ‖b.repr f i‖ₑ ^ τ) ^ (1 / τ) := by
  refine le_trans (le_of_eq ?_) (ENNReal.rpow_tsum_rpow_le (fun i => ‖b.repr f i‖ₑ) hτ0 hτ2)
  have hP : ‖f‖ₑ ^ 2 = ∑' i, ‖b.repr f i‖ₑ ^ 2 := by
    rw [← b.repr.eNorm_map, lp.enorm_sq_eq_tsum]
  simp_rw [ENNReal.rpow_two]
  rw [← hP, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- The weights of the dyadic blocks: `2^(k(1 - τ/2)) (2^k x²)^(τ/2) = 2^k x^τ`. -/
private theorem dyadicWeight_mul_rpow_eq {τ : ℝ} (hτ0 : 0 < τ) (k : ℕ) (x : ℝ≥0∞) :
    dyadicWeight (1 - τ / 2) k * (2 ^ k * x ^ 2) ^ (τ / 2) = 2 ^ k * x ^ τ := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ τ / 2)]
  have h1 : ((2 : ℝ≥0∞) ^ k) ^ (τ / 2) = dyadicWeight (τ / 2) k := by
    simpa using natCast_two_pow_rpow (τ / 2) k
  have h2 : (x ^ 2) ^ (τ / 2) = x ^ τ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    push_cast
    ring
  have h3 : dyadicWeight (1 - τ / 2) k * dyadicWeight (τ / 2) k = 2 ^ k := by
    rw [← dyadicWeight_add, sub_add_cancel, dyadicWeight_eq_pow, ENNReal.rpow_one]
  rw [h1, h2, ← mul_assoc, h3]

/-- `θ τ = 1 - τ/2` for `θ = 1/τ - 1/2`. -/
private theorem one_div_sub_mul_self {τ : ℝ} (hτ0 : 0 < τ) : (1 / τ - 1 / 2) * τ = 1 - τ / 2 := by
  field_simp

/-- **The dyadic sum of the errors**: `∑_k 2^(kθτ) E_{2^k}(f)^τ ≤ K ∑_i |⟨e_i, f⟩|^τ` with
`K = 2 · 2^(τ/2) (1 - 2^(-(1 - τ/2)))⁻¹`, for `0 < τ < 2`. The dyadic upper bound, the
subadditivity of `x ↦ x^(τ/2)` and Hardy's inequality for tails reduce the sum to
`∑_l 2^l (γ*_{2^l})^τ`, at most `2 ∑_i γ_i^τ`
(`tsum_two_pow_mul_decreasingRearrangement_le_two_mul`). -/
theorem tsum_approxSeqDyadic_nTerm_rpow_le {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) (f : H) :
    ∑' k, (nTerm b.coeffDictionary).approxSeqDyadic (1 / τ - 1 / 2) f k ^ τ ≤
      2 ^ (τ / 2) * (1 - 2 ^ (-(1 - τ / 2)))⁻¹ * 2 * ∑' i, ‖b.repr f i‖ₑ ^ τ := by
  set c := TauCeti.decreasingRearrangement fun i => ‖b.repr f i‖
  set v : ℕ → ℝ≥0∞ := fun j => (2 ^ j * ENNReal.ofReal (c (2 ^ j)) ^ 2) ^ (τ / 2)
  have hτ2' : 0 ≤ τ / 2 := by positivity
  have hE : ∀ k, (nTerm b.coeffDictionary).approxError f (2 ^ k) ^ τ ≤
      2 ^ (τ / 2) * ∑' l, v (k + l) := fun k => by
    calc (nTerm b.coeffDictionary).approxError f (2 ^ k) ^ τ
        = ((nTerm b.coeffDictionary).approxError f (2 ^ k) ^ 2) ^ (τ / 2) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; congr 1; push_cast; ring
      _ ≤ (2 * ∑' l, 2 ^ (k + l) * ENNReal.ofReal (c (2 ^ (k + l))) ^ 2) ^ (τ / 2) := by
          gcongr; exact b.approxError_nTerm_two_pow_sq_le k f
      _ ≤ 2 ^ (τ / 2) * ∑' l, v (k + l) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hτ2']
          gcongr
          exact ENNReal.rpow_tsum_le_tsum_rpow _ (by positivity) (by linarith)
  have hHardy := hardy_tail_le (le_refl (1 : ℝ≥0∞)) (1 - τ / 2) v
  simp only [lqNorm_one] at hHardy
  have hv : ∀ k, dyadicWeight (1 - τ / 2) k * v k = 2 ^ k * ENNReal.ofReal (c (2 ^ k)) ^ τ :=
    fun k => dyadicWeight_mul_rpow_eq hτ0 k _
  simp_rw [hv] at hHardy
  have h2 := tsum_two_pow_mul_decreasingRearrangement_le_two_mul
    (fun i => norm_nonneg (b.repr f i)) (b.tendsto_norm_repr f) hτ0
  simp only [ofReal_norm] at h2
  calc ∑' k, (nTerm b.coeffDictionary).approxSeqDyadic (1 / τ - 1 / 2) f k ^ τ
      = ∑' k, dyadicWeight (1 - τ / 2) k *
          (nTerm b.coeffDictionary).approxError f (2 ^ k) ^ τ := by
        simp_rw [approxSeqDyadic_rpow hτ0.le, one_div_sub_mul_self hτ0]
    _ ≤ ∑' k, dyadicWeight (1 - τ / 2) k * (2 ^ (τ / 2) * ∑' l, v (k + l)) := by
        gcongr with k; exact hE k
    _ = 2 ^ (τ / 2) * ∑' k, dyadicWeight (1 - τ / 2) k * ∑' l, v (k + l) := by
        rw [← ENNReal.tsum_mul_left]; congr 1; funext k; ring
    _ ≤ 2 ^ (τ / 2) * ((1 - 2 ^ (-(1 - τ / 2)))⁻¹ * (2 * ∑' i, ‖b.repr f i‖ₑ ^ τ)) := by
        gcongr; exact hHardy.trans (by gcongr)
    _ = _ := by ring

/-- **Stechkin–DeVore, upper bound**: for `0 < τ < 2` and `θ = 1/τ - 1/2`, the dyadic quasi-norm
of `A^θ_τ` for `n`-term approximation satisfies
`‖f‖_{A^θ_τ} ≤ C_τ (∑_i |⟨e_i, f⟩|^τ)^(1/τ)` (`HilbertBasis.stechkinConst`; Stechkin 1955 for
`τ = 1`; in general Pietsch, *Approximation spaces*, 1981, Example 1 in §3.2, and DeVore,
*Nonlinear approximation*, 1998, Theorem 4). -/
theorem approxNormDyadic_nTerm_le {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) (f : H) :
    (nTerm b.coeffDictionary).approxNormDyadic (1 / τ - 1 / 2) (ENNReal.ofReal τ) f ≤
      stechkinConst τ * (∑' i, ‖b.repr f i‖ₑ ^ τ) ^ (1 / τ) := by
  have hq0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.2 hτ0).ne'
  rw [approxNormDyadic, stechkinConst, add_mul, one_mul,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / τ)]
  gcongr
  · exact b.enorm_le_tsum_repr_rpow hτ0 hτ2.le f
  · rw [lqNorm_eq_tsum hq0 ofReal_ne_top, ENNReal.toReal_ofReal hτ0.le]
    gcongr
    exact b.tsum_approxSeqDyadic_nTerm_rpow_le hτ0 hτ2 f

/-- **Stechkin–DeVore, lower bound**: for `τ > 0` and `θ = 1/τ - 1/2`,
`∑_i |⟨e_i, f⟩|^τ ≤ 4 ‖f‖^τ_{A^θ_τ}` for the dyadic quasi-norm; the theorem uses it for
`τ < 2`, where `θ > 0`. The upper block inequality
bounds `∑_i γ_i^τ` by `(γ*_0)^τ + (γ*_1)^τ + ∑_l 2^(l+1) (γ*_{2^(l+1)})^τ`; the first two terms
are at most `‖f‖^τ`, and the dyadic lower bound gives
`2^(l+1) (γ*_{2^(l+1)})^τ ≤ 2 (2^(lθ) E_{2^l}(f))^τ`. -/
theorem tsum_repr_rpow_le {τ : ℝ} (hτ0 : 0 < τ) (f : H) :
    ∑' i, ‖b.repr f i‖ₑ ^ τ ≤
      4 * (nTerm b.coeffDictionary).approxNormDyadic (1 / τ - 1 / 2) (ENNReal.ofReal τ) f ^ τ := by
  set c := TauCeti.decreasingRearrangement fun i => ‖b.repr f i‖
  set N := (nTerm b.coeffDictionary).approxNormDyadic (1 / τ - 1 / 2) (ENNReal.ofReal τ) f
  set L := lqNorm (ENNReal.ofReal τ) ((nTerm b.coeffDictionary).approxSeqDyadic (1 / τ - 1 / 2) f)
  have hq0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.2 hτ0).ne'
  have hτ2' : 0 ≤ τ / 2 := by positivity
  have hc : ∀ n, ENNReal.ofReal (c n) ≤ ‖f‖ₑ := fun n => by
    rw [← ofReal_norm]; gcongr; exact b.decreasingRearrangement_norm_repr_le f n
  have hblock : ∀ l, 2 ^ (l + 1) * ENNReal.ofReal (c (2 ^ (l + 1))) ^ τ ≤
      2 * (nTerm b.coeffDictionary).approxSeqDyadic (1 / τ - 1 / 2) f l ^ τ := fun l => by
    have hE : ((nTerm b.coeffDictionary).approxError f (2 ^ l) ^ 2) ^ (τ / 2) =
        (nTerm b.coeffDictionary).approxError f (2 ^ l) ^ τ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; congr 1; push_cast; ring
    rw [approxSeqDyadic_rpow hτ0.le, one_div_sub_mul_self hτ0, ← hE]
    calc 2 ^ (l + 1) * ENNReal.ofReal (c (2 ^ (l + 1))) ^ τ
        = 2 * (dyadicWeight (1 - τ / 2) l *
            (2 ^ l * ENNReal.ofReal (c (2 ^ (l + 1))) ^ 2) ^ (τ / 2)) := by
          rw [dyadicWeight_mul_rpow_eq hτ0]; ring
      _ ≤ 2 * (dyadicWeight (1 - τ / 2) l *
            ((nTerm b.coeffDictionary).approxError f (2 ^ l) ^ 2) ^ (τ / 2)) := by
          gcongr; exact b.two_pow_mul_decreasingRearrangement_sq_le l f
  have hL : L ^ τ = ∑' l, (nTerm b.coeffDictionary).approxSeqDyadic (1 / τ - 1 / 2) f l ^ τ := by
    have h := lqNorm_rpow hq0 ofReal_ne_top
      ((nTerm b.coeffDictionary).approxSeqDyadic (1 / τ - 1 / 2) f)
    rwa [ENNReal.toReal_ofReal hτ0.le] at h
  have hfN : ‖f‖ₑ ^ τ ≤ N ^ τ := by gcongr; exact enorm_le_approxNormDyadic f
  have hLN : L ^ τ ≤ N ^ τ := by gcongr; exact lqNorm_le_approxNormDyadic f
  have h1 := tsum_rpow_le_decreasingRearrangement (fun i => norm_nonneg (b.repr f i))
    (b.tendsto_norm_repr f) hτ0
  simp only [ofReal_norm] at h1
  rw [tsum_eq_zero_add' CompleteLattice.summable] at h1
  calc ∑' i, ‖b.repr f i‖ₑ ^ τ
      ≤ ENNReal.ofReal (c 0) ^ τ + (2 ^ 0 * ENNReal.ofReal (c (2 ^ 0)) ^ τ +
          ∑' l, 2 ^ (l + 1) * ENNReal.ofReal (c (2 ^ (l + 1))) ^ τ) := h1
    _ ≤ ‖f‖ₑ ^ τ + (‖f‖ₑ ^ τ + 2 * L ^ τ) := by
        gcongr
        · exact hc 0
        · simpa using ENNReal.rpow_le_rpow (hc 1) hτ0.le
        · rw [hL, ← ENNReal.tsum_mul_left]; exact tsum_le_tsum hblock
    _ ≤ N ^ τ + (N ^ τ + 2 * N ^ τ) := by gcongr
    _ = 4 * N ^ τ := by ring

/-- **The theorem of Stechkin and DeVore** on best `n`-term approximation from a Hilbert basis:
for `0 < τ < 2` and `θ = 1/τ - 1/2`, `f` lies in the approximation space `A^θ_τ` of
`n`-term approximation from the basis iff its coefficients lie in `ℓ_τ`,
`∑_i |⟨e_i, f⟩|^τ < ∞`. The range `τ < 1`, where `A^θ_τ` is only quasi-normed, is included.
Stechkin (Dokl. Akad. Nauk SSSR 102, 1955) proved the case `τ = 1`. For general `τ` the
sequence form goes back to Pietsch (*Approximation spaces*, J. Approx. Theory 1981, Example 1 in
§3.2), and DeVore (*Nonlinear approximation*, Acta Numer. 1998, Theorem 4) proves it by
interpolation. -/
theorem memApprox_nTerm_iff {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) (f : H) :
    (nTerm b.coeffDictionary).MemApprox (1 / τ - 1 / 2) (ENNReal.ofReal τ) f ↔
      ∑' i, ‖b.repr f i‖ₑ ^ τ < ∞ := by
  have hθ : 0 ≤ 1 / τ - 1 / 2 := by
    have : 1 / 2 < 1 / τ := one_div_lt_one_div_of_lt hτ0 hτ2
    linarith
  rw [memApprox_iff_approxNormDyadic_lt_top' (ENNReal.ofReal_pos.2 hτ0).ne' hθ]
  constructor
  · intro h
    exact (b.tsum_repr_rpow_le hτ0 f).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.rpow_lt_top_of_nonneg hτ0.le h.ne))
  · intro h
    exact (b.approxNormDyadic_nTerm_le hτ0 hτ2 f).trans_lt
      (ENNReal.mul_lt_top (stechkinConst_ne_top hτ0 hτ2).lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) h.ne))

end HilbertBasis
