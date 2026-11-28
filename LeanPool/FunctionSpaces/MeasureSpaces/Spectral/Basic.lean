/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Jackson
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Spectral schemes and Sobolev spaces in a Hilbert space

A **spectral scheme** in a complex Hilbert space `H` is a Hilbert basis `(e_i)_{i ∈ ι}` together
with a **level** `lvl : ι → ℕ` with finite level sets (`SpectralScheme`).  The approximants of
complexity `n` are the combinations of the basis elements of level `< n`,

`A n = span {e_i : lvl i < n}`.

Examples: the Fourier basis of `L_2(𝕋^d)` with `lvl k = max_i |k_i|`; an eigenbasis of a
Laplacian on a compact manifold with `lvl` the integer part of the square root of the
eigenvalue.

The **Sobolev space** of order `s ≥ 0` is the image of `ℓ²(ι)` under the diagonal operator

`J_s c = ∑_i (1 + lvl i)^(-s) c_i e_i`   (`SpectralScheme.sobolevEmbed`),

with the norm of `ℓ²`: `f ∈ H^s` iff `∑_i (1 + lvl i)^(2s) |⟨e_i, f⟩|² < ∞`
(`mem_range_sobolevEmbed_iff`).  This is the Bessel-potential description of `L_2` Sobolev
spaces; it needs no new normed space, since `ℓ²` already is one.

By Parseval's identity both approximation inequalities hold with constant `1`:

* **Jackson**: `E_n(J_s c) ≤ n^(-s) ‖c‖` (`jacksonBound`), since the error of the truncation to
  levels `< n` involves only coefficients of level `≥ n`;
* **Bernstein**: every `a ∈ A n` is `J_s c` with `‖c‖ ≤ n^s ‖a‖` (`liftBound`), since `a` has
  only coefficients of level `< n`.

So `J_s` is a smoothness space of order `s` for the scheme (`toSmoothnessSpace`).
-/

@[expose] public section

open scoped ENNReal InnerProductSpace lp

/-- A **spectral scheme**: a Hilbert basis with a level function whose level sets are finite. -/
structure SpectralScheme (ι H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Hilbert basis. -/
  basis : HilbertBasis ι ℂ H
  /-- The level of a basis element. -/
  level : ι → ℕ
  finite_level : ∀ n, {i | level i < n}.Finite

namespace SpectralScheme

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (S : SpectralScheme ι H)

/-- The approximants of complexity `n`: combinations of basis elements of level `< n`. -/
noncomputable def span (n : ℕ) : Submodule ℂ H := Submodule.span ℂ (S.basis '' {i | S.level i < n})

/-- `A_0 = {0}`: no basis element has level `< 0`. -/
@[simp]
theorem span_zero : S.span 0 = ⊥ := by simp [span]

/-- The spans increase with `n`. -/
theorem span_mono : Monotone S.span := fun _ _ h =>
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/-- The spectral scheme as an approximation scheme. -/
noncomputable def toScheme : ApproximationScheme H :=
  ApproximationScheme.ofSubmodules (fun n => (S.span n).restrictScalars ℝ) (by simp)
    (fun _ _ h => S.span_mono h)

/-- The approximants of the spectral scheme are the spans. -/
@[simp]
theorem mem_toScheme {n : ℕ} {a : H} : a ∈ S.toScheme n ↔ a ∈ S.span n := Iff.rfl

/-- An approximant of complexity `n` has no coefficients of level `≥ n`. -/
theorem repr_eq_zero_of_mem_span {n : ℕ} {a : H} (ha : a ∈ S.span n) {i : ι}
    (hi : n ≤ S.level i) : S.basis.repr a i = 0 := by
  rw [S.basis.repr_apply_apply]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      rintro rfl; exact absurd hj (not_lt.2 hi)
    exact S.basis.orthonormal.2 hij
  · simp
  · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
  · intro c x _ hx; rw [inner_smul_right, hx, mul_zero]

/-- The **truncation** of `f` to levels `< n`, `∑_{lvl i < n} ⟨e_i, f⟩ e_i`, an approximant. -/
noncomputable def truncate (n : ℕ) (f : H) : H :=
  ∑ i ∈ (S.finite_level n).toFinset, S.basis.repr f i • S.basis i

/-- The truncation `P_n f` lies in `A_n`. -/
theorem truncate_mem_span (n : ℕ) (f : H) : S.truncate n f ∈ S.span n :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)

/-- The coefficients of `truncate n f` are those of `f` at levels `< n`. -/
theorem repr_truncate (n : ℕ) (f : H) (i : ι) :
    S.basis.repr (S.truncate n f) i = if S.level i < n then S.basis.repr f i else 0 := by
  classical
  rw [S.basis.repr_apply_apply, truncate]
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp S.basis.orthonormal, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The coefficients of `f - truncate n f` are those of `f` at levels `≥ n`. -/
theorem repr_sub_truncate (n : ℕ) (f : H) (i : ι) :
    S.basis.repr (f - S.truncate n f) i = if S.level i < n then 0 else S.basis.repr f i := by
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_truncate]
  split_ifs <;> simp

/-- The **weight** `(1 + lvl i)^s`. -/
noncomputable def weight (s : ℝ) (i : ι) : ℝ := ((1 + S.level i : ℕ) : ℝ) ^ s

/-- The weights `(1 + λ(i))^s` are positive. -/
theorem weight_pos (s : ℝ) (i : ι) : 0 < S.weight s i :=
  Real.rpow_pos_of_pos (by positivity) s

/-- For `s ≥ 0` the weights are at least `1`. -/
theorem one_le_weight {s : ℝ} (hs : 0 ≤ s) (i : ι) : 1 ≤ S.weight s i :=
  Real.one_le_rpow (by simp) hs

/-- The inverse weight as a complex number has modulus `(1 + λ(i))^(-s)`. -/
theorem norm_ofReal_inv_weight (s : ℝ) (i : ι) : ‖((S.weight s i)⁻¹ : ℂ)‖ = (S.weight s i)⁻¹ := by
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (S.weight_pos s i))]

/-- The weight as a complex number has modulus `(1 + λ(i))^s`. -/
theorem norm_ofReal_weight (s : ℝ) (i : ι) : ‖(S.weight s i : ℂ)‖ = S.weight s i := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.weight_pos s i)]

/-- The weights are nonzero. -/
theorem ofReal_weight_ne_zero (s : ℝ) (i : ι) : (S.weight s i : ℂ) ≠ 0 := by
  simpa using (S.weight_pos s i).ne'

/-- At level `≥ n` the inverse weight is at most `n^(-s)`. -/
theorem inv_weight_le {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) {i : ι} (hi : n ≤ S.level i) :
    (S.weight s i)⁻¹ ≤ (n : ℝ) ^ (-s) := by
  rw [weight, ← Real.rpow_neg (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn)
    (by exact_mod_cast (show n ≤ 1 + S.level i by omega)) (neg_nonpos.2 hs)

/-- At level `< n` the weight is at most `n^s`. -/
theorem weight_le {s : ℝ} (hs : 0 ≤ s) {n : ℕ} {i : ι} (hi : S.level i < n) :
    S.weight s i ≤ (n : ℝ) ^ s :=
  Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show 1 + S.level i ≤ n by omega)) hs

/-- The diagonal operator `c ↦ ((1 + lvl i)^(-s) c_i)_i` on `ℓ²`, a contraction for `s ≥ 0`. -/
noncomputable def diagInvWeight (s : ℝ) (hs : 0 ≤ s) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨fun i => ((S.weight s i)⁻¹ : ℂ) * c i,
        ((lp.memℓp c).norm).mono fun i => by
          rw [norm_mul, S.norm_ofReal_inv_weight]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (inv_le_one_of_one_le₀ (S.one_le_weight hs i))⟩
      map_add' := fun c c' => by
        ext i
        change ((S.weight s i)⁻¹ : ℂ) * (c + c') i =
          ((S.weight s i)⁻¹ : ℂ) * c i + ((S.weight s i)⁻¹ : ℂ) * c' i
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun a c => by
        ext i
        change ((S.weight s i)⁻¹ : ℂ) * (a • c) i = a * (((S.weight s i)⁻¹ : ℂ) * c i)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    1 fun c => by
      rw [one_mul]
      refine lp.norm_mono (by norm_num) fun i => ?_
      change ‖((S.weight s i)⁻¹ : ℂ) * c i‖ ≤ ‖c i‖
      rw [norm_mul, S.norm_ofReal_inv_weight]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (S.one_le_weight hs i))

/-- The diagonal operator multiplies the `i`-th coordinate by `(1 + λ(i))^(-s)`. -/
theorem diagInvWeight_apply (s : ℝ) (hs : 0 ≤ s) (c : ℓ²(ι, ℂ)) (i : ι) :
    S.diagInvWeight s hs c i = ((S.weight s i)⁻¹ : ℂ) * c i := rfl

/-- The **Sobolev embedding** `J_s c = ∑_i (1 + lvl i)^(-s) c_i e_i` of `ℓ²` into `H`; its
range is the Sobolev space of order `s`. -/
noncomputable def sobolevEmbed (s : ℝ) (hs : 0 ≤ s) : ℓ²(ι, ℂ) →L[ℂ] H :=
  (S.basis.repr.symm.toLinearIsometry.toContinuousLinearMap).comp (S.diagInvWeight s hs)

/-- The coefficients of `J_s c` are `(1 + λ(i))^(-s) c_i`. -/
theorem repr_sobolevEmbed (s : ℝ) (hs : 0 ≤ s) (c : ℓ²(ι, ℂ)) (i : ι) :
    S.basis.repr (S.sobolevEmbed s hs c) i = ((S.weight s i)⁻¹ : ℂ) * c i := by
  change S.basis.repr (S.basis.repr.symm (S.diagInvWeight s hs c)) i = _
  rw [LinearIsometryEquiv.apply_symm_apply, diagInvWeight_apply]

/-- `J_s` is injective. -/
theorem sobolevEmbed_injective (s : ℝ) (hs : 0 ≤ s) :
    Function.Injective (S.sobolevEmbed s hs) := fun c c' h => by
  ext i
  have := congrArg (fun f => S.basis.repr f i) h
  simp only [repr_sobolevEmbed] at this
  exact mul_left_cancel₀ (inv_ne_zero (S.ofReal_weight_ne_zero s i)) (by simpa using this)

/-- An element of `ℓ²` with prescribed weighted coefficients is mapped to `f`. -/
theorem sobolevEmbed_weighted (s : ℝ) (hs : 0 ≤ s) {f : H}
    (h : Memℓp (fun i => (S.weight s i : ℂ) * S.basis.repr f i) 2) :
    S.sobolevEmbed s hs ⟨_, h⟩ = f := by
  refine S.basis.repr.injective (lp.ext (funext fun i => ?_))
  rw [repr_sobolevEmbed]
  change ((S.weight s i)⁻¹ : ℂ) * ((S.weight s i : ℂ) * S.basis.repr f i) = S.basis.repr f i
  rw [← mul_assoc, inv_mul_cancel₀ (S.ofReal_weight_ne_zero s i), one_mul]

/-- **The Sobolev space as a set**: `f = J_s c` for some `c ∈ ℓ²` exactly when
`∑_i (1 + lvl i)^(2s) |⟨e_i, f⟩|² < ∞`. -/
theorem mem_range_sobolevEmbed_iff (s : ℝ) (hs : 0 ≤ s) (f : H) :
    f ∈ Set.range (S.sobolevEmbed s hs) ↔
      Memℓp (fun i => (S.weight s i : ℂ) * S.basis.repr f i) 2 := by
  constructor
  · rintro ⟨c, rfl⟩
    convert lp.memℓp c using 1
    funext i
    rw [repr_sobolevEmbed, ← mul_assoc, mul_inv_cancel₀ (S.ofReal_weight_ne_zero s i), one_mul]
  · intro h
    exact ⟨⟨_, h⟩, S.sobolevEmbed_weighted s hs h⟩

/-- **The truncation error of a Sobolev element**: `‖J_s c - P_n J_s c‖ ≤ n^(-s) ‖c‖` for
`n ≥ 1`, by Parseval's identity, since only the coefficients of level `≥ n` remain and
`(1 + lvl i)^(-s) ≤ n^(-s)` there. -/
theorem norm_sub_truncate_le (s : ℝ) (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) (c : ℓ²(ι, ℂ)) :
    ‖S.sobolevEmbed s hs c - S.truncate n (S.sobolevEmbed s hs c)‖ ≤ (n : ℝ) ^ (-s) * ‖c‖ := by
  set f := S.sobolevEmbed s hs c
  rw [← S.basis.repr.norm_map]
  calc ‖S.basis.repr (f - S.truncate n f)‖ ≤ ‖(((n : ℝ) ^ (-s) : ℝ) : ℂ) • c‖ := by
        refine lp.norm_mono (by norm_num) fun i => ?_
        rw [repr_sub_truncate, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        split_ifs with hi
        · simp only [norm_zero]; positivity
        · rw [repr_sobolevEmbed, norm_mul, norm_mul, S.norm_ofReal_inv_weight, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by positivity)]
          gcongr
          exact S.inv_weight_le hs hn (not_lt.1 hi)
    _ = (n : ℝ) ^ (-s) * ‖c‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Jackson's inequality** for the Sobolev space: `E_n(J_s c) ≤ n^(-s) ‖c‖`, with the
truncation as approximant (`SpectralScheme.norm_sub_truncate_le`). -/
theorem jacksonBound (s : ℝ) (hs : 0 ≤ s) :
    ApproximationScheme.JacksonBound ((S.sobolevEmbed s hs).restrictScalars ℝ) S.toScheme s 1 := by
  intro n hn c
  refine (ENNReal.toReal_mono eNorm_ne_top (ApproximationScheme.approxError_le_of_mem
    (S.truncate_mem_span n (S.sobolevEmbed s hs c)) _)).trans ?_
  rw [toReal_eNorm, one_mul]
  exact S.norm_sub_truncate_le s hs hn c

/-- **Bernstein's inequality** for the Sobolev space: every `a ∈ A n` is `J_s c` with
`‖c‖ ≤ n^s ‖a‖`. -/
theorem liftBound (s : ℝ) (hs : 0 ≤ s) :
    ApproximationScheme.LiftBound ((S.sobolevEmbed s hs).restrictScalars ℝ) S.toScheme s 1 := by
  intro n hn a ha
  have hle : ∀ i, ‖(S.weight s i : ℂ) * S.basis.repr a i‖ ≤
      (n : ℝ) ^ s * ‖S.basis.repr a i‖ := fun i => by
    rw [norm_mul, S.norm_ofReal_weight]
    by_cases hi : S.level i < n
    · gcongr; exact S.weight_le hs hi
    · rw [S.repr_eq_zero_of_mem_span ha (not_lt.1 hi)]; simp
  have hmem : Memℓp (fun i => (S.weight s i : ℂ) * S.basis.repr a i) 2 :=
    (((lp.memℓp (S.basis.repr a)).norm).const_mul ((n : ℝ) ^ s)).mono hle
  refine ⟨⟨_, hmem⟩, S.sobolevEmbed_weighted s hs hmem, ?_⟩
  rw [one_mul, ← S.basis.repr.norm_map]
  calc ‖(⟨_, hmem⟩ : ℓ²(ι, ℂ))‖ ≤ ‖(((n : ℝ) ^ s : ℝ) : ℂ) • S.basis.repr a‖ := by
        refine lp.norm_mono (by norm_num) fun i => ?_
        change ‖(S.weight s i : ℂ) * S.basis.repr a i‖ ≤
          ‖((((n : ℝ) ^ s : ℝ) : ℂ) • S.basis.repr a) i‖
        have hn0 : (0 : ℝ) < (n : ℝ) ^ s := Real.rpow_pos_of_pos (by exact_mod_cast hn) s
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul (((n : ℝ) ^ s : ℝ) : ℂ),
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0]
        exact hle i
    _ = (n : ℝ) ^ s * ‖S.basis.repr a‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **The Sobolev space of order `s > 0` is a smoothness space** for the spectral scheme, with
Jackson and Bernstein constants `1`. -/
noncomputable def toSmoothnessSpace (s : ℝ) (hs : 0 < s) :
    ApproximationScheme.SmoothnessSpace S.toScheme ℓ²(ι, ℂ) where
  incl := (S.sobolevEmbed s hs.le).restrictScalars ℝ
  injective := S.sobolevEmbed_injective s hs.le
  order := s
  order_pos := hs
  jacksonConst := 1
  jacksonConst_nonneg := zero_le_one
  bernsteinConst := 1
  bernsteinConst_nonneg := zero_le_one
  jackson := S.jacksonBound s hs.le
  bernstein := S.liftBound s hs.le

end SpectralScheme
