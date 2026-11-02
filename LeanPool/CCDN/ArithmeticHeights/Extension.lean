/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.Arakelov
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Heights under a finite extension of number fields

Mathlib's `Height.mulHeight` is the height **relative** to the field it is computed over. This
file proves how it changes when that field grows: for a finite extension `L / K` of number
fields and a tuple `x` over `K`,

`mulHeight x ^ [L : K] = mulHeight (algebraMap K L ∘ x)`.

Equivalently, `mulHeight x ^ (finrank ℚ K)⁻¹` does not depend on the field the coordinates are
read in — the statement that the *absolute* height is well defined, recorded here for a single
element as `NumberField.absMulHeight₁_eq`.

## Main results

* `NumberField.mulHeight_pow_finrank` and `NumberField.mulHeight₁_pow_finrank`: the tuple and
  one-variable forms of the displayed identity.
* `NumberField.finrank_nsmul_logHeight` and `NumberField.finrank_nsmul_logHeight₁`: the
  logarithmic forms, where the power becomes an `nsmul`.
* `NumberField.absMulHeight₁_eq`: over *any* number field `K` containing it, the absolute height
  of `x` is `mulHeight₁ x ^ (finrank ℚ K : ℝ)⁻¹`. This is the classical statement that the
  absolute height does not depend on the field of definition, and
  `NumberField.absMulHeight₁_pow_finrank` is the same identity with a natural-number exponent.
  `NumberField.absLogHeight₁_eq` is its logarithmic form: the absolute logarithmic height is the
  relative one divided by the degree.

## Implementation notes

The two factors of the height are handled by different mechanisms, and neither is the
places-above-places bookkeeping one might expect.

The **archimedean** factor is first turned into a product over the complex embeddings — this is
what `InfinitePlace.card_filter_mk_eq` does, the exponent `mult v` being the number of embeddings
inducing `v`. The statement then becomes the count `#{φ : L →+* ℂ | φ.comp (algebraMap K L) = ψ}
= [L : K]`, which is `AlgHom.card` once `ℂ` carries the `K`-algebra structure of `ψ`. The
roadmap asks for `InfinitePlace.liesOver_iff_comap_eq` as the first step of this layer; it is not
needed on this route, and Mathlib meanwhile carries that theory itself, in
`Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean`.

The **nonarchimedean** factor of the height of an *integral* tuple is the inverse of the absolute
norm of the ideal its coordinates generate, by
`NumberField.absNorm_mul_finprod_finitePlace_eq_one`. So that half reduces to
`Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ [L : K]`, which is
`Ideal.relNorm_algebraMap` followed by `Ideal.absNorm_relNorm` — no ramification or inertia
appears, since those are already inside Mathlib's relative ideal norm.

⚠ The nonarchimedean factor alone is **not** invariant under scaling: `∏ᶠ v, ⨆ i, v (c * x i)`
picks up the finite part of the product formula for `c`. The reduction from an arbitrary tuple to
an integral one is therefore performed on the whole height, where
`Height.mulHeight_smul_eq_mulHeight` applies to both sides at once, and not factor by factor.

## References

These are the statements of
[mathlib4#41606](https://github.com/leanprover-community/mathlib4/pull/41606) and carry its
names, so that adopting Mathlib's version is a deletion plus an import.

This is Layer 0.3 of the `ArithmeticHeights` roadmap.
-/

public section

namespace NumberField

open Finset Function Height InfinitePlace Module

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {ι : Type*} [Finite ι]

/-!
### The archimedean factor

A product over the infinite places, weighted by `mult`, is a product over the complex embeddings;
in that form the extension statement is the count of extensions of an embedding.
-/

section Archimedean

/-- A `mult`-weighted product over the infinite places is the product over the complex
embeddings, each place counted once per embedding inducing it. -/
lemma prod_embeddings_eq {M : Type*} [CommMonoid M] (f : InfinitePlace K → M) :
    ∏ φ : K →+* ℂ, f (InfinitePlace.mk φ) = ∏ w : InfinitePlace K, f w ^ w.mult := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ ↦ f (InfinitePlace.mk φ))]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
    Finset.prod_const, card_filter_mk_eq]

open scoped Classical in
/-- Every complex embedding of `K` has exactly `[L : K]` extensions to `L`. -/
private lemma card_filter_comp_eq (ψ : K →+* ℂ) :
    #{φ : L →+* ℂ | φ.comp (algebraMap K L) = ψ} = finrank K L := by
  let : Algebra K ℂ := ψ.toAlgebra
  rw [← AlgHom.card K L ℂ]
  refine (Finset.card_nbij AlgHom.toRingHom (fun σ _ ↦ ?_) AlgHom.toRingHom_injective.injOn
    (fun φ hφ ↦ ?_)).symm
  · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and]
    ext r
    simp [RingHom.algebraMap_toAlgebra]
  · simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hφ
    exact ⟨⟨φ, fun r ↦ by simp [RingHom.algebraMap_toAlgebra, ← hφ]⟩, mem_univ _, rfl⟩

open scoped Classical in
/-- A product over the complex embeddings of `L` of a factor that reads an embedding only through
its restriction to `K` is the `[L : K]`-th power of the product over the embeddings of `K`. -/
lemma prod_comp_eq_prod_pow (F : (K →+* ℂ) → ℝ) :
    ∏ φ : L →+* ℂ, F (φ.comp (algebraMap K L)) = (∏ ψ : K →+* ℂ, F ψ) ^ finrank K L := by
  rw [← Finset.prod_fiberwise Finset.univ (fun φ : L →+* ℂ ↦ φ.comp (algebraMap K L))
    (fun φ ↦ F (φ.comp (algebraMap K L))), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun ψ _ ↦ ?_
  rw [Finset.prod_congr rfl (fun φ hφ ↦ by rw [(Finset.mem_filter.mp hφ).2]),
    Finset.prod_const, card_filter_comp_eq]

/-- **The archimedean half of every extension formula for a height.** A `mult`-weighted product
over the infinite places of `L` of a local factor `g` that reads a place only through its
restriction to `K` is the `[L : K]`-th power of the corresponding product over `K`. The two
normalizations of Layer 0 differ in `g` and in nothing else, so both take this lemma as it
stands. -/
theorem prod_infinitePlace_pow_mult_eq (f : InfinitePlace K → ℝ) (g : InfinitePlace L → ℝ)
    (h : ∀ φ : L →+* ℂ, g (InfinitePlace.mk φ) = f (InfinitePlace.mk (φ.comp (algebraMap K L)))) :
    ∏ w : InfinitePlace L, g w ^ w.mult = (∏ v : InfinitePlace K, f v ^ v.mult) ^ finrank K L := by
  rw [← prod_embeddings_eq (K := L) g, ← prod_embeddings_eq (K := K) f,
    ← prod_comp_eq_prod_pow (fun ψ ↦ f (InfinitePlace.mk ψ))]
  exact Finset.prod_congr rfl fun φ _ ↦ h φ

omit [Finite ι] in
private lemma prod_infinitePlace_algebraMap (x : ι → K) :
    ∏ w : InfinitePlace L, (⨆ i, w (algebraMap K L (x i))) ^ w.mult =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) ^ finrank K L :=
  prod_infinitePlace_pow_mult_eq _ _ fun φ ↦ iSup_congr fun i ↦ by simp [InfinitePlace.apply]

end Archimedean

/-!
### The nonarchimedean factor

For an integral tuple this factor is the inverse of the absolute norm of the ideal the
coordinates generate, so the extension statement is one about ideal norms.
-/

section NonArchimedean

private lemma absNorm_map_eq (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ finrank K L := by
  rw [← Ideal.absNorm_relNorm (𝓞 K), Ideal.relNorm_algebraMap, map_pow,
    IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]

omit [NumberField K] [NumberField L] in
private lemma coe_algebraMap_ringOfIntegers (a : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 L) a : 𝓞 L) : L) = algebraMap K L (a : K) :=
  (IsScalarTower.algebraMap_apply K K L a).symm

private lemma finprod_finitePlace_algebraMap_int {y : ι → 𝓞 K} (hy : y ≠ 0) :
    ∏ᶠ w : FinitePlace L, ⨆ i, w (algebraMap K L (y i : K)) =
      (∏ᶠ v : FinitePlace K, ⨆ i, v (y i : K)) ^ finrank K L := by
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
  have hy' : (fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (hinj (h.trans (map_zero _).symm))⟩
  have hspan : Ideal.span (Set.range fun i ↦ algebraMap (𝓞 K) (𝓞 L) (y i)) =
      (Ideal.span (Set.range y)).map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hK := absNorm_mul_finprod_finitePlace_eq_one hy
  have hL := absNorm_mul_finprod_finitePlace_eq_one hy'
  rw [hspan, absNorm_map_eq] at hL
  simp_rw [coe_algebraMap_ringOfIntegers (L := L)] at hL
  have hN : ((Ideal.span (Set.range y)).absNorm : ℝ) ≠ 0 := by
    have : Ideal.span (Set.range y) ≠ ⊥ := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      exact fun h ↦ hi (by simpa using (Ideal.span_eq_bot.mp h) (y i) ⟨i, rfl⟩)
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr this
  refine mul_left_cancel₀ (pow_ne_zero (finrank K L) hN) ?_
  rw [← mul_pow, hK, one_pow]
  exact_mod_cast hL

end NonArchimedean

/-!
### The extension formula
-/

/-- Every tuple over a number field is a nonzero multiple of an integral one. -/
private lemma exists_integer_tuple (x : ι → K) :
    ∃ (d : K) (y : ι → 𝓞 K), d ≠ 0 ∧ ∀ i, (y i : K) = d * x i := by
  have := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset ι) x
  refine ⟨algebraMap (𝓞 K) K (b : 𝓞 K), fun i ↦ (hb i (Finset.mem_univ i)).choose, ?_, fun i ↦ ?_⟩
  · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr
      (nonZeroDivisors.coe_ne_zero b)
  · have h := (hb i (Finset.mem_univ i)).choose_spec
    rw [show (((hb i (Finset.mem_univ i)).choose : 𝓞 K) : K)
      = algebraMap (𝓞 K) K (hb i (Finset.mem_univ i)).choose from rfl, h, Algebra.smul_def]

private lemma mulHeight_pow_finrank_int (y : ι → 𝓞 K) :
    Height.mulHeight (fun i ↦ (y i : K)) ^ finrank K L
      = Height.mulHeight (fun i ↦ algebraMap K L (y i : K)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hz : (fun i ↦ (y i : K)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, by simpa using hi⟩
  have hz' : (fun i ↦ algebraMap K L (y i : K)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (FaithfulSMul.algebraMap_injective K L
      (by simpa using h))⟩
  rw [NumberField.mulHeight_eq hz, NumberField.mulHeight_eq hz', mul_pow,
    prod_infinitePlace_algebraMap (L := L), finprod_finitePlace_algebraMap_int hy]

/-- **The height over `L` is the `[L : K]`-th power of the height over `K`.** The relative height
grows with the field the tuple is read in, by exactly the degree. -/
theorem mulHeight_pow_finrank (x : ι → K) :
    Height.mulHeight x ^ finrank K L = Height.mulHeight (algebraMap K L ∘ x) := by
  obtain ⟨d, y, hd, hy⟩ := exists_integer_tuple (K := K) x
  have hd' : algebraMap K L d ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr hd
  have h1 : (fun i ↦ (y i : K)) = d • x := funext fun i ↦ by rw [hy i]; rfl
  have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
    funext i
    simp [hy i]
  have e1 : Height.mulHeight (fun i ↦ (y i : K)) = Height.mulHeight x :=
    h1 ▸ Height.mulHeight_smul_eq_mulHeight x hd
  have e2 : Height.mulHeight (fun i ↦ algebraMap K L (y i : K))
      = Height.mulHeight (algebraMap K L ∘ x) :=
    h2 ▸ Height.mulHeight_smul_eq_mulHeight _ hd'
  rw [← e1, ← e2]
  exact mulHeight_pow_finrank_int y

/-- The one-variable form of `NumberField.mulHeight_pow_finrank`. -/
theorem mulHeight₁_pow_finrank (x : K) :
    Height.mulHeight₁ x ^ finrank K L = Height.mulHeight₁ (algebraMap K L x) := by
  rw [Height.mulHeight₁_eq_mulHeight, Height.mulHeight₁_eq_mulHeight,
    mulHeight_pow_finrank (L := L)]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The logarithmic form of `NumberField.mulHeight_pow_finrank`. -/
theorem finrank_nsmul_logHeight (x : ι → K) :
    finrank K L • Height.logHeight x = Height.logHeight (algebraMap K L ∘ x) := by
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
    ← mulHeight_pow_finrank (L := L), Real.log_pow, nsmul_eq_mul]

/-- The logarithmic form of `NumberField.mulHeight₁_pow_finrank`. -/
theorem finrank_nsmul_logHeight₁ (x : K) :
    finrank K L • Height.logHeight₁ x = Height.logHeight₁ (algebraMap K L x) := by
  rw [Height.logHeight₁_eq_log_mulHeight₁, Height.logHeight₁_eq_log_mulHeight₁,
    ← mulHeight₁_pow_finrank (L := L), Real.log_pow, nsmul_eq_mul]

open scoped Classical IntermediateField in
/-- **The absolute height does not depend on the field of definition.** Mathlib defines
`absMulHeight₁ x` through `ℚ⟮x⟯`; this computes it in any number field containing `x`. -/
theorem absMulHeight₁_eq (x : K) :
    absMulHeight₁ x = Height.mulHeight₁ x ^ (finrank ℚ K : ℝ)⁻¹ := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
  have : NumberField ℚ⟮x⟯ := {}
  rw [absMulHeight₁, dite_eq_left_of_eq_true (eq_true hx)]
  have key : Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ x) ^ finrank ℚ⟮x⟯ K
      = Height.mulHeight₁ x := mulHeight₁_pow_finrank _
  have hpos : (0 : ℝ) ≤ Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ x) :=
    le_trans zero_le_one (Height.one_le_mulHeight₁ _)
  rw [← key, ← Real.rpow_natCast _ (finrank ℚ⟮x⟯ K), ← Real.rpow_mul hpos]
  congr 1
  rw [← Module.finrank_mul_finrank ℚ ℚ⟮x⟯ K]
  have h1 : (Module.finrank ℚ ℚ⟮x⟯ : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := ℚ⟮x⟯)).ne'
  have h2 : (Module.finrank ℚ⟮x⟯ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ⟮x⟯) (M := K)).ne'
  push_cast
  field_simp

/-- The relative height is the `[K : ℚ]`-th power of the absolute one: `absMulHeight₁_eq` read
backwards, in the form that carries a natural-number exponent rather than a real one. -/
theorem absMulHeight₁_pow_finrank (x : K) :
    absMulHeight₁ x ^ finrank ℚ K = Height.mulHeight₁ x := by
  rw [absMulHeight₁_eq, ← Real.rpow_natCast _ (finrank ℚ K),
    ← Real.rpow_mul (Height.mulHeight₁_nonneg x), inv_mul_cancel₀, Real.rpow_one]
  exact Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne'

/-- The logarithmic form of `NumberField.absMulHeight₁_eq`: the absolute logarithmic height is
the relative one divided by the degree. -/
theorem absLogHeight₁_eq (x : K) :
    absLogHeight₁ x = Height.logHeight₁ x / finrank ℚ K := by
  rw [absLogHeight₁, absMulHeight₁_eq, Real.log_rpow (Height.mulHeight₁_pos x),
    Height.logHeight₁_eq_log_mulHeight₁, inv_mul_eq_div]

/-!
### The Arakelov normalization

`NumberField.arakelovMulHeight` differs from `Height.mulHeight` only in the archimedean local
factor, and that factor reads a place in exactly the same way, so the two counts above prove the
extension formula for it too. The nonarchimedean factor is literally the same expression, and the
reduction to an integral tuple is the same reduction.
-/

section Arakelov

variable {κ : Type*} [Fintype κ]

/-- `√S ^ n = S ^ (n / 2)`. The Arakelov local factor carries the real exponent `mult v / 2`
while `prod_infinitePlace_pow_mult_eq` carries the natural power `mult v`; this moves between
them. -/
private lemma sqrt_pow_eq_rpow {S : ℝ} (hS : 0 ≤ S) (n : ℕ) :
    Real.sqrt S ^ n = S ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (S ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul hS]
  congr 1
  ring

private lemma prod_infinitePlace_arakelov_algebraMap (x : κ → K) :
    ∏ w : InfinitePlace L, (∑ i, w (algebraMap K L (x i)) ^ 2) ^ ((w.mult : ℝ) / 2) =
      (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ ((v.mult : ℝ) / 2)) ^ finrank K L := by
  have key := prod_infinitePlace_pow_mult_eq (K := K) (L := L)
    (fun v ↦ Real.sqrt (∑ i, v (x i) ^ 2))
    (fun w ↦ Real.sqrt (∑ i, w (algebraMap K L (x i)) ^ 2))
    (fun φ ↦ congrArg Real.sqrt
      (Finset.sum_congr rfl fun i _ ↦ by simp [InfinitePlace.apply]))
  calc ∏ w : InfinitePlace L, (∑ i, w (algebraMap K L (x i)) ^ 2) ^ ((w.mult : ℝ) / 2)
      = ∏ w : InfinitePlace L, Real.sqrt (∑ i, w (algebraMap K L (x i)) ^ 2) ^ w.mult :=
        Finset.prod_congr rfl fun w _ ↦ (sqrt_pow_eq_rpow (by positivity) w.mult).symm
    _ = (∏ v : InfinitePlace K, Real.sqrt (∑ i, v (x i) ^ 2) ^ v.mult) ^ finrank K L := key
    _ = _ := by
        congr 1
        exact Finset.prod_congr rfl fun v _ ↦ sqrt_pow_eq_rpow (by positivity) v.mult

private lemma arakelovMulHeight_pow_finrank_int (y : κ → 𝓞 K) :
    arakelovMulHeight (fun i ↦ (y i : K)) ^ finrank K L
      = arakelovMulHeight (fun i ↦ algebraMap K L (y i : K)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [show (fun _ : κ ↦ (0 : K)) = 0 from rfl, show (fun _ : κ ↦ (0 : L)) = 0 from rfl]
  have hz : (fun i ↦ (y i : K)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨i, by simpa using hi⟩
  have hz' : (fun i ↦ algebraMap K L (y i : K)) ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    exact Function.ne_iff.mpr ⟨i, fun h ↦ hi (FaithfulSMul.algebraMap_injective K L
      (by simpa using h))⟩
  rw [arakelovMulHeight_eq hz, arakelovMulHeight_eq hz', mul_pow,
    prod_infinitePlace_arakelov_algebraMap (L := L), finprod_finitePlace_algebraMap_int hy]

/-- **The Arakelov height over `L` is the `[L : K]`-th power of the Arakelov height over `K`**,
the companion of `NumberField.mulHeight_pow_finrank` in the normalization of Layer 0.1. Only the
archimedean factor has to be redone, and only through the local factor it reads off a place. -/
theorem arakelovMulHeight_pow_finrank (x : κ → K) :
    arakelovMulHeight x ^ finrank K L = arakelovMulHeight (algebraMap K L ∘ x) := by
  obtain ⟨d, y, hd, hy⟩ := exists_integer_tuple (K := K) x
  have hd' : algebraMap K L d ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr hd
  have h1 : (fun i ↦ (y i : K)) = d • x := funext fun i ↦ by rw [hy i]; rfl
  have h2 : (fun i ↦ algebraMap K L (y i : K)) = algebraMap K L d • (algebraMap K L ∘ x) := by
    funext i
    simp [hy i]
  have e1 : arakelovMulHeight (fun i ↦ (y i : K)) = arakelovMulHeight x :=
    h1 ▸ arakelovMulHeight_smul_eq x hd
  have e2 : arakelovMulHeight (fun i ↦ algebraMap K L (y i : K))
      = arakelovMulHeight (algebraMap K L ∘ x) :=
    h2 ▸ arakelovMulHeight_smul_eq _ hd'
  rw [← e1, ← e2]
  exact arakelovMulHeight_pow_finrank_int y

/-- The logarithmic form of `NumberField.arakelovMulHeight_pow_finrank`. -/
theorem finrank_nsmul_arakelovLogHeight (x : κ → K) :
    finrank K L • arakelovLogHeight x = arakelovLogHeight (algebraMap K L ∘ x) := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovLogHeight_eq_log_arakelovMulHeight,
    ← arakelovMulHeight_pow_finrank (L := L), Real.log_pow, nsmul_eq_mul]

end Arakelov

/-!
### Worked examples

The special case `K = ℚ` is the acceptance test the roadmap names for the general statement: it
needs no places above places, and it is literally an instance.
-/

section Examples

/-- `H_K(x) = H_ℚ(x) ^ [K : ℚ]` for a rational tuple. -/
example {K : Type*} [Field K] [NumberField K] {ι : Type*} [Finite ι] (x : ι → ℚ) :
    Height.mulHeight x ^ finrank ℚ K = Height.mulHeight (algebraMap ℚ K ∘ x) :=
  mulHeight_pow_finrank x

/-- A concrete value: `H_ℚ(3/4) = 4` by `Rat.mulHeight₁_eq_max`, so over a number field of
degree `d` the same number has height `4 ^ d`. -/
example {K : Type*} [Field K] [NumberField K] :
    Height.mulHeight₁ (algebraMap ℚ K (3 / 4)) = 4 ^ finrank ℚ K := by
  rw [← mulHeight₁_pow_finrank, Rat.mulHeight₁_eq_max]
  norm_num

end Examples

end NumberField

end
