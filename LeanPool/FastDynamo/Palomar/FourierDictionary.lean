/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.Statement
public import LeanPool.FastDynamo.Dynamics.VanishingDiffusivity.ProductBridge

/-!
# The Fourier dictionary of the Challenge statement

The Challenge statement (`FastDynamo/Palomar/Statement.lean`) reads every field on mathlib's
torus `T3 = UnitAddTorus (Fin 3)` through mathlib's Fourier coefficients
`mFourierCoeff f m = ∫ e^{-2πi m·x} f(x) dx`, while the library reads `L²` fields on its literal
three-torus `Torus 3` through the basis pairings `literalFourierCoeff Φ m i = ⟪e_m, Φᵢ⟫`.

The two settings share their types: `Torus 3` is the abbreviation `UnitAddTorus (Fin 3)`, so
`T3` and `Torus 3` are the same type, and both `L2` and `LiteralC3L2` are the abbreviation
`Lp C3 2 (volume : Measure (UnitAddTorus (Fin 3)))`.  No transport is needed between them
(`l2_eq_literalC3L2`).  What differs is the measure inside `mFourierCoeff`, which mathlib takes to
be the product of the Haar probability measures `AddCircle.haarAddCircle`; it is the `volume` of
`T3` (`volume_unitAddTorus_eq_haar`), so `mFourierCoeff` only sees `volume`-classes
(`mFourierCoeff_congr_ae`).

## Contents

* `mFourierCoeff_congr_ae`, `mFourierCoeff_eq_integral_volume` — the measure inside
  `mFourierCoeff`.
* `mFourierCoeff_coe_eq_inner` — for a scalar class `f`, `mFourierCoeff f m = ⟪e_m, f⟫`.
* `literalFourierCoeff_eq_mFourierCoeff`, `productCoeffCLM_eq_mFourierCoeff` — the library's
  coefficients in the Challenge's form (the first is a simp lemma: for fields of `L2` the
  Challenge's form is the normal form).
* `l2Coeff m i : L2 →L[ℂ] ℂ` — the coefficient `B ↦ B̂ᵢ(m)` as a continuous linear functional,
  with the simp lemmas `mFourierCoeff_l2_add`, `…_smul`, `…_neg`, `…_sub`, `…_zero`, `…_sum`.
* `l2_ext_mFourierCoeff`, `l2_eq_zero_iff` — Fourier injectivity on `L2`.
* `hasSum_inner_l2`, `hasSum_norm_sq_l2`, `inner_l2_eq_tsum`, `norm_sq_l2_eq_tsum` — Parseval and
  Plancherel in coordinates.
* `mFourierCoeff_gradChar`, `inner_gradChar` — the gradient characters.
* `mem_L2σ_iff` — the characterisation `B ∈ L2σ ↔ ∀ m, ∑ᵢ mᵢ B̂ᵢ(m) = 0` stated in the docstring
  of `L2σ`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus
open scoped ComplexConjugate

/-! ## The types -/

/-- The Challenge's `L²(𝕋³;ℂ³)` is the library's `L²` space of the literal three-torus; the two
are the same abbreviation, so this is `rfl`, and no identification map is needed. -/
theorem l2_eq_literalC3L2 : L2 = LiteralC3L2 := rfl

/-- The Challenge's torus is the library's literal three-torus, by `rfl`. -/
theorem t3_eq_torus : T3 = Torus 3 := rfl

/-! ## The measure inside `mFourierCoeff` -/

/-- `mFourierCoeff` on `T3` is integration against the conjugate character for the `volume` of
`T3`. -/
theorem mFourierCoeff_eq_integral_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : T3 → E) (m : Fin 3 → ℤ) :
    mFourierCoeff f m = ∫ x, mFourier (-m) x • f x := by
  change ∫ x, mFourier (-m) x • f x ∂(torusHaarMeasure (Fin 3)) = _
  rw [← volume_unitAddTorus_eq_haar]

/-- `mFourierCoeff` on `T3` depends only on the `volume`-class of the function. -/
theorem mFourierCoeff_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : T3 → E} (h : f =ᵐ[volume] g) (m : Fin 3 → ℤ) :
    mFourierCoeff f m = mFourierCoeff g m := by
  rw [mFourierCoeff_eq_integral_volume, mFourierCoeff_eq_integral_volume]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- For a scalar `L²` class, the Fourier coefficient is the pairing with the Fourier basis
vector. -/
theorem mFourierCoeff_coe_eq_inner (f : FlatTorus3ScalarL2) (m : Fin 3 → ℤ) :
    mFourierCoeff (f : T3 → ℂ) m = inner ℂ (flatTorus3FourierBasis m) f := by
  rw [mFourierCoeff_eq_integral_volume, inner_flatTorus3FourierBasis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul, mFourier_neg]

/-! ## The library's coefficients in the Challenge's form -/

/-- The `i`-th coordinate class of a field has the coordinate coefficients of the field. -/
@[simp] theorem mFourierCoeff_literalCoordL2 (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (literalCoordL2 i B : T3 → ℂ) m = mFourierCoeff (fun x ↦ B x i) m :=
  mFourierCoeff_congr_ae (literalCoordL2_coe_ae i B) m

/-- **F1.**  The library's literal Fourier coefficient `⟪e_m, Bᵢ⟫` is mathlib's Fourier
coefficient of the `i`-th coordinate. -/
@[simp] theorem literalFourierCoeff_eq_mFourierCoeff (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    literalFourierCoeff B m i = mFourierCoeff (fun x ↦ B x i) m := by
  rw [literalFourierCoeff, ← mFourierCoeff_coe_eq_inner, mFourierCoeff_literalCoordL2]

/-- The product Fourier coefficient at `(n, k)` of a field of the product model is mathlib's
Fourier coefficient at `Fin.snoc n k` of the transported field. -/
theorem productCoeffCLM_eq_mFourierCoeff (n : TransverseFrequency) (k : ℤ) (i : Fin 3)
    (W : ProductC3L2) :
    productCoeffCLM n k i W =
      mFourierCoeff (fun x ↦ (toLiteralC3L2 W : L2) x i) (Fin.snoc n k : Fin 3 → ℤ) := by
  rw [← literalFourierCoeff_eq_mFourierCoeff, literalFourierCoeff_toLiteralC3L2]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The product Fourier coefficients of the field `toLiteralC3L2.symm B` are the Challenge's
coefficients of `B`. -/
theorem productCoeffCLM_toLiteralC3L2_symm_eq_mFourierCoeff (n : TransverseFrequency) (k : ℤ)
    (i : Fin 3) (B : L2) :
    productCoeffCLM n k i (toLiteralC3L2.symm B) =
      mFourierCoeff (fun x ↦ B x i) (Fin.snoc n k : Fin 3 → ℤ) := by
  rw [productCoeffCLM_eq_mFourierCoeff, LinearIsometryEquiv.apply_symm_apply]

/-- The library's coefficient at the frequency `m`, written with the transverse part
`fun j ↦ m j.castSucc` and the axial part `m 2`, as a Challenge coefficient. -/
theorem productCoeffCLM_split_eq_mFourierCoeff (m : Fin 3 → ℤ) (i : Fin 3) (W : ProductC3L2) :
    productCoeffCLM (fun j : Fin 2 ↦ m j.castSucc) (m 2) i W =
      mFourierCoeff (fun x ↦ (toLiteralC3L2 W : L2) x i) m := by
  rw [← literalFourierCoeff_eq_mFourierCoeff, literalFourierCoeff_toLiteralC3L2]
  rfl

/-! ## The coefficient functionals -/

/-- The coefficient `B ↦ B̂ᵢ(m) = mFourierCoeff (fun x ↦ B x i) m` as a continuous linear
functional on `L²(𝕋³;ℂ³)`. -/
def l2Coeff (m : Fin 3 → ℤ) (i : Fin 3) : L2 →L[ℂ] ℂ :=
  (innerSL ℂ (flatTorus3FourierBasis m)).comp (literalCoordL2 i)

/-- Evaluation of the coefficient functional. -/
@[simp] theorem l2Coeff_apply (m : Fin 3 → ℤ) (i : Fin 3) (B : L2) :
    l2Coeff m i B = mFourierCoeff (fun x ↦ B x i) m := by
  rw [← literalFourierCoeff_eq_mFourierCoeff]
  rfl

/-- The coefficients of a sum of fields. -/
@[simp↓] theorem mFourierCoeff_l2_add (B C : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (B + C : L2) x i) m =
      mFourierCoeff (fun x ↦ B x i) m + mFourierCoeff (fun x ↦ C x i) m := by
  simp only [← l2Coeff_apply, map_add]

/-- The coefficients of a scalar multiple of a field. -/
@[simp↓] theorem mFourierCoeff_l2_smul (c : ℂ) (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (c • B : L2) x i) m = c * mFourierCoeff (fun x ↦ B x i) m := by
  simp only [← l2Coeff_apply, map_smul, smul_eq_mul]

/-- The coefficients of a negated field. -/
@[simp↓] theorem mFourierCoeff_l2_neg (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (-B : L2) x i) m = -mFourierCoeff (fun x ↦ B x i) m := by
  simp only [← l2Coeff_apply, map_neg]

/-- The coefficients of a difference of fields. -/
@[simp↓] theorem mFourierCoeff_l2_sub (B C : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (B - C : L2) x i) m =
      mFourierCoeff (fun x ↦ B x i) m - mFourierCoeff (fun x ↦ C x i) m := by
  simp only [← l2Coeff_apply, map_sub]

/-- The coefficients of the zero field vanish. -/
@[simp↓] theorem mFourierCoeff_l2_zero (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (0 : L2) x i) m = 0 := by
  simp only [← l2Coeff_apply, map_zero]

/-- The coefficients of a finite sum of fields. -/
@[simp↓] theorem mFourierCoeff_l2_sum {ι : Type*} (s : Finset ι) (B : ι → L2) (m : Fin 3 → ℤ)
    (i : Fin 3) :
    mFourierCoeff (fun x ↦ (∑ k ∈ s, B k : L2) x i) m =
      ∑ k ∈ s, mFourierCoeff (fun x ↦ B k x i) m := by
  simp only [← l2Coeff_apply, map_sum]

/-! ### Simp forms

`simp` rewrites the coercion `⇑(B + C : L2)` through the underlying almost-everywhere classes
(`AddSubgroup.coe_add` and its siblings) when it visits the subterms.  The lemmas
`mFourierCoeff_l2_add` and its siblings are therefore pre-simp lemmas (`simp↓`), which fire before
the subterms are visited; the lemmas below catch the forms already rewritten through the classes. -/

/-- The coefficients of a sum of fields, in `simp`-normal form. -/
@[simp] theorem mFourierCoeff_aeeqFun_add (B C : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ ((B : T3 →ₘ[volume] C3) + (C : T3 →ₘ[volume] C3)) x i) m =
      mFourierCoeff (fun x ↦ B x i) m + mFourierCoeff (fun x ↦ C x i) m :=
  mFourierCoeff_l2_add B C m i

/-- The coefficients of a negated field, in `simp`-normal form. -/
@[simp] theorem mFourierCoeff_aeeqFun_neg (B : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (-(B : T3 →ₘ[volume] C3)) x i) m =
      -mFourierCoeff (fun x ↦ B x i) m :=
  mFourierCoeff_l2_neg B m i

/-- The coefficients of a difference of fields, in `simp`-normal form. -/
@[simp] theorem mFourierCoeff_aeeqFun_sub (B C : L2) (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ ((B : T3 →ₘ[volume] C3) - (C : T3 →ₘ[volume] C3)) x i) m =
      mFourierCoeff (fun x ↦ B x i) m - mFourierCoeff (fun x ↦ C x i) m :=
  mFourierCoeff_l2_sub B C m i

/-- The coefficients of a finite sum of fields, in `simp`-normal form. -/
@[simp] theorem mFourierCoeff_aeeqFun_sum {ι : Type*} (s : Finset ι) (B : ι → L2)
    (m : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ (∑ k ∈ s, (B k : T3 →ₘ[volume] C3)) x i) m =
      ∑ k ∈ s, mFourierCoeff (fun x ↦ B k x i) m := by
  rw [← mFourierCoeff_l2_sum, AddSubgroup.val_finsetSum]

/-- The Fourier coefficients of the zero function vanish. -/
@[simp] theorem mFourierCoeff_fun_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (m : Fin 3 → ℤ) : mFourierCoeff (fun _ : T3 ↦ (0 : E)) m = 0 := by
  simp [mFourierCoeff]

/-! ## Fourier injectivity -/

/-- **F2, injectivity.**  Two fields of `L²(𝕋³;ℂ³)` with the same coordinate Fourier
coefficients are equal. -/
theorem l2_ext_mFourierCoeff {B C : L2}
    (h : ∀ m i, mFourierCoeff (fun x ↦ B x i) m = mFourierCoeff (fun x ↦ C x i) m) : B = C :=
  literalC3L2_ext_literalFourierCoeff fun m i ↦ by
    simp only [literalFourierCoeff_eq_mFourierCoeff]
    exact h m i

/-- A field of `L²(𝕋³;ℂ³)` vanishes if and only if all its coordinate Fourier coefficients
vanish. -/
theorem l2_eq_zero_iff {B : L2} : B = 0 ↔ ∀ m i, mFourierCoeff (fun x ↦ B x i) m = 0 := by
  refine ⟨fun h m i ↦ by rw [h, mFourierCoeff_l2_zero], fun h ↦ l2_ext_mFourierCoeff ?_⟩
  intro m i
  rw [h, mFourierCoeff_l2_zero]

/-! ## Parseval and Plancherel -/

/-- The inner product of `L²(𝕋³;ℂ³)` is the sum of the inner products of the coordinates. -/
theorem inner_l2_eq_sum_inner_literalCoordL2 (B C : L2) :
    inner ℂ B C = ∑ i, inner ℂ (literalCoordL2 i B) (literalCoordL2 i C) := by
  simp only [MeasureTheory.L2.inner_def]
  rw [← integral_finsetSum _ fun i _ ↦ L2.integrable_inner _ _]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun i ↦ literalCoordL2_coe_ae i B,
    ae_all_iff.2 fun i ↦ literalCoordL2_coe_ae i C] with x hB hC
  simp only [PiLp.inner_apply, hB, hC]

/-- **F2, Parseval.**  The inner product of two fields of `L²(𝕋³;ℂ³)` is the sum over the
frequencies of `∑ᵢ conj (B̂ᵢ(m)) Ĉᵢ(m)`. -/
theorem hasSum_inner_l2 (B C : L2) :
    HasSum (fun m : Fin 3 → ℤ ↦ ∑ i, conj (mFourierCoeff (fun x ↦ B x i) m) *
      mFourierCoeff (fun x ↦ C x i) m) (inner ℂ B C) := by
  rw [inner_l2_eq_sum_inner_literalCoordL2]
  refine hasSum_sum fun i _ ↦ ?_
  convert flatTorus3FourierBasis.hasSum_inner_mul_inner (literalCoordL2 i B)
    (literalCoordL2 i C) using 2 with m
  rw [← mFourierCoeff_literalCoordL2, ← mFourierCoeff_literalCoordL2,
    mFourierCoeff_coe_eq_inner, mFourierCoeff_coe_eq_inner, inner_conj_symm]

/-- **F2, Plancherel.**  `‖B‖² = ∑_m ∑ᵢ ‖B̂ᵢ(m)‖²` for `B ∈ L²(𝕋³;ℂ³)`. -/
theorem hasSum_norm_sq_l2 (B : L2) :
    HasSum (fun m : Fin 3 → ℤ ↦ ∑ i, ‖mFourierCoeff (fun x ↦ B x i) m‖ ^ 2) (‖B‖ ^ 2) := by
  have h := (hasSum_inner_l2 B B).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, Complex.re_sum, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re] at h
  convert h using 1
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rfl

/-- Parseval as an equality of sums. -/
theorem inner_l2_eq_tsum (B C : L2) :
    inner ℂ B C = ∑' m : Fin 3 → ℤ, ∑ i, conj (mFourierCoeff (fun x ↦ B x i) m) *
      mFourierCoeff (fun x ↦ C x i) m :=
  (hasSum_inner_l2 B C).tsum_eq.symm

/-- Plancherel as an equality of sums. -/
theorem norm_sq_l2_eq_tsum (B : L2) :
    ‖B‖ ^ 2 = ∑' m : Fin 3 → ℤ, ∑ i, ‖mFourierCoeff (fun x ↦ B x i) m‖ ^ 2 :=
  (hasSum_norm_sq_l2 B).tsum_eq.symm

/-- The squared coefficients of a field of `L²(𝕋³;ℂ³)` are summable. -/
theorem summable_norm_sq_l2 (B : L2) :
    Summable fun m : Fin 3 → ℤ ↦ ∑ i, ‖mFourierCoeff (fun x ↦ B x i) m‖ ^ 2 :=
  (hasSum_norm_sq_l2 B).summable

/-- The squared coefficients of a single coordinate of a field of `L²(𝕋³;ℂ³)` are summable. -/
theorem summable_norm_sq_l2_coord (B : L2) (i : Fin 3) :
    Summable fun m : Fin 3 → ℤ ↦ ‖mFourierCoeff (fun x ↦ B x i) m‖ ^ 2 :=
  (summable_norm_sq_l2 B).of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    fun m ↦ Finset.single_le_sum (f := fun j ↦ ‖mFourierCoeff (fun x ↦ B x j) m‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

/-! ## The gradient characters -/

/-- The `i`-th coordinate of `gradChar m` is `mᵢ e_m`. -/
theorem literalCoordL2_gradChar (m : Fin 3 → ℤ) (i : Fin 3) :
    literalCoordL2 i (gradChar m) = (m i : ℂ) • flatTorus3FourierBasis m := by
  refine Lp.ext ?_
  filter_upwards [literalCoordL2_coe_ae i (gradChar m),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure T3)
      (mFourier m • ContinuousMap.const T3 (WithLp.toLp 2 fun i ↦ (m i : ℂ) : C3)),
    Lp.coeFn_smul (m i : ℂ) (flatTorus3FourierBasis m), flatTorus3FourierBasis_coe_ae m]
    with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h4, gradChar, h2]
  simp [mul_comm]

/-- **The coefficients of the gradient characters**: `(gradChar m)ᵢ^(n) = mᵢ` at `n = m` and `0`
otherwise. -/
@[simp] theorem mFourierCoeff_gradChar (m n : Fin 3 → ℤ) (i : Fin 3) :
    mFourierCoeff (fun x ↦ gradChar m x i) n = if n = m then (m i : ℂ) else 0 := by
  rw [← mFourierCoeff_literalCoordL2, literalCoordL2_gradChar, mFourierCoeff_coe_eq_inner,
    inner_smul_right, orthonormal_iff_ite.1 flatTorus3FourierBasis.orthonormal n m]
  split_ifs <;> simp

/-- Pairing a field with a gradient character: `⟪gradChar m, B⟫ = ∑ᵢ mᵢ B̂ᵢ(m)`. -/
theorem inner_gradChar (m : Fin 3 → ℤ) (B : L2) :
    inner ℂ (gradChar m) B = ∑ i, (m i : ℂ) * mFourierCoeff (fun x ↦ B x i) m := by
  rw [inner_l2_eq_sum_inner_literalCoordL2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [literalCoordL2_gradChar, inner_smul_left, ← mFourierCoeff_coe_eq_inner,
    mFourierCoeff_literalCoordL2, map_intCast]

/-! ## The solenoidal subspace -/

/-- **The characterisation of `L2σ`** stated in its docstring: `B ∈ L²_σ` if and only if
`∑ᵢ mᵢ B̂ᵢ(m) = 0` for every `m ∈ ℤ³`. -/
theorem mem_L2σ_iff (B : L2) :
    B ∈ L2σ ↔ ∀ m : Fin 3 → ℤ, ∑ i, (m i : ℂ) * mFourierCoeff (fun x ↦ B x i) m = 0 := by
  simp_rw [← inner_gradChar]
  constructor
  · intro hB m
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self m)) hB
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 fun u hu ↦ ?_
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact h m
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

end

end FastDynamo
