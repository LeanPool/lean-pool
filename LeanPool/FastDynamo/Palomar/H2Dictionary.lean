/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.FourierDictionary
public import LeanPool.FastDynamo.Analysis.ProductH2DenseEmbedding

/-!
# The `H²` dictionary of the Challenge statement

The Challenge statement says that a field `B` lies in `H²(𝕋³;ℂ³)` (`MemH2`) when
`∑_m |m|⁴ |B̂(m)|² < ∞`.  The library realises `H²` on the product torus as the closed Fourier
graph `ProductC3H2`: a pair `(V, a)` of a product `L²` field and an array `a` of weighted
coefficients with `aᵢ(n, k) = (1 + 4π²(|n|² + k²)) V̂ᵢ(n, k)`, square-summable in the nested
`ℓ²` space.  The weights `|m|⁴` and `(1 + 4π²|m|²)²` are comparable up to an `L²` term, so a field
of `L2` satisfies `MemH2` exactly when its product preimage carries a weighted certificate.

## Contents

* `memH2_congr_ae` — `MemH2` depends only on the `volume`-class of the field.
* `memH2_iff_forall_summable_weighted` — `MemH2` of a field of `L2` as summability of the
  weighted product coefficients of its preimage.
* `memH2_iff_exists_productH2`, `memH2_toLiteralC3L2_iff` — **H**: `MemH2 ⇑B` if and only if
  `B` is the transport of a field of the product `H²` graph.
* `productH2OfMemH2` — the product `H²` field of a field with `MemH2`, and
  `toLiteralC3L2_productH2Embedding_productH2OfMemH2`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus

/-- `MemH2` depends only on the `volume`-class of the field. -/
theorem memH2_congr_ae {B C : T3 → C3} (h : B =ᵐ[volume] C) : MemH2 B ↔ MemH2 C := by
  have hc : ∀ (m : Fin 3 → ℤ) (i : Fin 3),
      mFourierCoeff (fun x ↦ B x i) m = mFourierCoeff (fun x ↦ C x i) m := fun m i ↦
    mFourierCoeff_congr_ae (by filter_upwards [h] with x hx; rw [hx]) m
  simp only [MemH2, hc]

/-- The joint product frequency `(k, n)` as a frequency of `ℤ³`: `n` transverse, `k` axial. -/
def productFrequencyEquiv : ProductNestedFrequency ≃ (Fin 3 → ℤ) where
  toFun q := Fin.snoc q.2 q.1
  invFun m := (m (Fin.last 2), fun j : Fin 2 ↦ m j.castSucc)
  left_inv q := by
    rcases q with ⟨k, n⟩
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
  right_inv m := Fin.snoc_init_self m

/-- Evaluation of `productFrequencyEquiv`. -/
@[simp] theorem productFrequencyEquiv_apply (q : ProductNestedFrequency) :
    productFrequencyEquiv q = (Fin.snoc q.2 q.1 : Fin 3 → ℤ) :=
  rfl

/-- The squared length of the frequency `Fin.snoc n k`. -/
theorem sum_sq_snoc (n : TransverseFrequency) (k : ℤ) :
    (∑ i, (((Fin.snoc n k : Fin 3 → ℤ) i : ℤ) : ℝ) ^ 2) = (∑ j, (n j : ℝ) ^ 2) + (k : ℝ) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The library's `H²` weight at the frequency `(n, k)` is `1 + 4π²|m|²` at `m = Fin.snoc n k`. -/
theorem productH2Weight_eq (n : TransverseFrequency) (k : ℤ) :
    productH2Weight n k =
      1 + (2 * Real.pi) ^ 2 * ∑ i, (((Fin.snoc n k : Fin 3 → ℤ) i : ℤ) : ℝ) ^ 2 := by
  rw [sum_sq_snoc, productH2Weight]

/-- **`MemH2` in the library's weights.**  A field `B` of `L2` satisfies `MemH2` exactly when, for
every component `i`, the weighted product coefficients `w(n, k) V̂ᵢ(n, k)` of its preimage
`V = toLiteralC3L2.symm B` are square-summable over the joint frequencies `(k, n)`. -/
theorem memH2_iff_forall_summable_weighted (B : L2) :
    MemH2 ⇑B ↔ ∀ i : Fin 3, Summable fun q : ProductNestedFrequency ↦
      ‖(productH2Weight q.2 q.1 : ℂ) * productCoeffCLM q.2 q.1 i (toLiteralC3L2.symm B)‖ ^ 2 := by
  set c : Fin 3 → (Fin 3 → ℤ) → ℂ := fun i m ↦ mFourierCoeff (fun x ↦ B x i) m with hc_def
  set s : (Fin 3 → ℤ) → ℝ := fun m ↦ ∑ i, ((m i : ℤ) : ℝ) ^ 2 with hs_def
  have hs0 : ∀ m, 0 ≤ s m := fun m ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hcoeff : ∀ (q : ProductNestedFrequency) (i : Fin 3),
      ‖(productH2Weight q.2 q.1 : ℂ) * productCoeffCLM q.2 q.1 i (toLiteralC3L2.symm B)‖ ^ 2 =
        (1 + (2 * Real.pi) ^ 2 * s (productFrequencyEquiv q)) ^ 2 *
          ‖c i (productFrequencyEquiv q)‖ ^ 2 := by
    intro q i
    rw [productCoeffCLM_toLiteralC3L2_symm_eq_mFourierCoeff, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, productH2Weight_eq]
    rfl
  simp_rw [hcoeff]
  have hmem : MemH2 ⇑B ↔ Summable fun q : ProductNestedFrequency ↦
      s (productFrequencyEquiv q) ^ 2 * ∑ i, ‖c i (productFrequencyEquiv q)‖ ^ 2 := by
    rw [MemH2]
    exact (productFrequencyEquiv.summable_iff (f := fun m : Fin 3 → ℤ ↦
      s m ^ 2 * ∑ i, ‖c i m‖ ^ 2)).symm
  have hl2 : ∀ i, Summable fun q : ProductNestedFrequency ↦ ‖c i (productFrequencyEquiv q)‖ ^ 2 :=
    fun i ↦ (productFrequencyEquiv.summable_iff (f := fun m : Fin 3 → ℤ ↦ ‖c i m‖ ^ 2)).2
      (summable_norm_sq_l2_coord B i)
  rw [hmem]
  constructor
  · intro h i
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun q ↦ ?_)
      (((hl2 i).mul_left 2).add (h.mul_left (2 * ((2 * Real.pi) ^ 2) ^ 2)))
    set e := productFrequencyEquiv q
    have hi : ‖c i e‖ ^ 2 ≤ ∑ j, ‖c j e‖ ^ 2 :=
      Finset.single_le_sum (f := fun j ↦ ‖c j e‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
        (Finset.mem_univ i)
    have hb : 0 ≤ (2 * Real.pi) ^ 2 * s e := mul_nonneg (by positivity) (hs0 e)
    have hsq : (1 + (2 * Real.pi) ^ 2 * s e) ^ 2 ≤ 2 + 2 * ((2 * Real.pi) ^ 2 * s e) ^ 2 := by
      nlinarith [sq_nonneg ((2 * Real.pi) ^ 2 * s e - 1)]
    have hci : 0 ≤ ‖c i e‖ ^ 2 := sq_nonneg _
    calc (1 + (2 * Real.pi) ^ 2 * s e) ^ 2 * ‖c i e‖ ^ 2
        ≤ (2 + 2 * ((2 * Real.pi) ^ 2 * s e) ^ 2) * ‖c i e‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq hci
      _ ≤ 2 * ‖c i e‖ ^ 2 + 2 * ((2 * Real.pi) ^ 2) ^ 2 * (s e ^ 2 * ∑ j, ‖c j e‖ ^ 2) := by
          have : 0 ≤ 2 * ((2 * Real.pi) ^ 2) ^ 2 * s e ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hi this]
  · intro h
    refine Summable.of_nonneg_of_le
      (fun q ↦ mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (fun q ↦ ?_) (summable_sum (s := Finset.univ) fun i _ ↦ h i)
    set e := productFrequencyEquiv q
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h1 : s e ≤ 1 + (2 * Real.pi) ^ 2 * s e := by nlinarith [hs0 e]
    exact pow_le_pow_left₀ (hs0 e) h1 2

/-- The weighted coefficient array of a field with `MemH2`, flattened over the joint
frequencies. -/
def memH2WeightedFlat {B : L2} (hB : MemH2 ⇑B) (i : Fin 3) :
    lp (fun _ : ProductNestedFrequency ↦ ℂ) 2 :=
  ⟨fun q ↦ (productH2Weight q.2 q.1 : ℂ) * productCoeffCLM q.2 q.1 i (toLiteralC3L2.symm B),
    memℓp_gen <| by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (memH2_iff_forall_summable_weighted B).1 hB i⟩

/-- **The product `H²` field of a field with `MemH2`**: the preimage `toLiteralC3L2.symm B` with
its weighted coefficient certificate. -/
def productH2OfMemH2 {B : L2} (hB : MemH2 ⇑B) : ProductC3H2 :=
  ⟨(toLiteralC3L2.symm B,
      WithLp.toLp 2 fun i ↦ productScalarFourierNestedFlat.symm (memH2WeightedFlat hB i)), by
    rw [mem_productH2Submodule_iff]
    intro n k i
    rfl⟩

/-- The field of `productH2OfMemH2 hB` is the preimage of `B`. -/
theorem productH2Embedding_productH2OfMemH2 {B : L2} (hB : MemH2 ⇑B) :
    productH2Embedding (productH2OfMemH2 hB) = toLiteralC3L2.symm B :=
  rfl

/-- Transporting the field of `productH2OfMemH2 hB` returns `B`. -/
theorem toLiteralC3L2_productH2Embedding_productH2OfMemH2 {B : L2} (hB : MemH2 ⇑B) :
    toLiteralC3L2 (productH2Embedding (productH2OfMemH2 hB)) = B := by
  rw [productH2Embedding_productH2OfMemH2, LinearIsometryEquiv.apply_symm_apply]

/-- **H.**  A field `B` of `L²(𝕋³;ℂ³)` satisfies the Challenge's `MemH2` exactly when it is the
transport of a field of the library's product `H²` graph. -/
theorem memH2_iff_exists_productH2 (B : L2) :
    MemH2 ⇑B ↔ ∃ W : ProductC3H2, toLiteralC3L2 (productH2Embedding W) = B := by
  refine ⟨fun hB ↦ ⟨productH2OfMemH2 hB, toLiteralC3L2_productH2Embedding_productH2OfMemH2 hB⟩, ?_⟩
  rintro ⟨W, rfl⟩
  rw [memH2_iff_forall_summable_weighted, LinearIsometryEquiv.symm_apply_apply]
  intro i
  have h := (lp.memℓp (productScalarFourierNestedFlat (productH2WeightedCoeffs W i))).summable
    (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, productScalarFourierNestedFlat_apply,
    productH2WeightedCoeffs_apply] at h
  exact h

/-- **H, product form.**  The transport of a product `L²` field satisfies `MemH2` exactly when the
field lies in the product `H²` graph. -/
theorem memH2_toLiteralC3L2_iff (V : ProductC3L2) :
    MemH2 ⇑(toLiteralC3L2 V : L2) ↔ ∃ W : ProductC3H2, productH2Embedding W = V := by
  rw [memH2_iff_exists_productH2]
  exact exists_congr fun W ↦ toLiteralC3L2.injective.eq_iff

/-- The transport of the field of a product `H²` element satisfies `MemH2`. -/
theorem memH2_toLiteralC3L2_productH2Embedding (W : ProductC3H2) :
    MemH2 ⇑(toLiteralC3L2 (productH2Embedding W) : L2) :=
  (memH2_toLiteralC3L2_iff _).2 ⟨W, rfl⟩

end

end FastDynamo
