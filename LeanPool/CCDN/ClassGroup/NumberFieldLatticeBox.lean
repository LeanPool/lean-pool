/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.IntegerTranslationClassPacking
import LeanPool.CCDN.ClassGroup.LatticeFinitePacking
import LeanPool.CCDN.ClassGroup.NumberFieldEuclideanLattice

/-! Finite-radius counting for the algebraic integers. The input
is a short independent integral basis over the reals; it is not required
to generate the ring of integers over `ℤ`. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory

private theorem unitBall_volume_le_two_pow_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    volume.real (Metric.ball (0 : E) 1) ≤ (2 : ℝ) ^ Module.finrank ℝ E := by
  let c := stdOrthonormalBasis ℝ E
  let e : E → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun x ↦ (MeasurableEquiv.toLp 2 _).symm (c.repr x)
  have hm : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).comp
      c.measurePreserving_repr
  let U : Set (Fin (Module.finrank ℝ E) → ℝ) := Set.Icc (fun _ ↦ -1) (fun _ ↦ 1)
  have hvol : volume (e ⁻¹' U) = (2 : ENNReal) ^ Module.finrank ℝ E := by
    rw [hm.measure_preimage (show MeasurableSet U from measurableSet_Icc).nullMeasurableSet]
    norm_num [U, Real.volume_Icc_pi]
  have hsub : Metric.ball (0 : E) 1 ⊆ e ⁻¹' U := by
    intro x hx
    have hnorm : ‖x‖ < 1 := by simpa using hx
    have hcoord (i : Fin (Module.finrank ℝ E)) : |e x i| ≤ 1 := by
      have hi := PiLp.norm_apply_le (c.repr x) i
      rw [c.repr.norm_map] at hi
      exact hi.trans hnorm.le
    exact ⟨fun i ↦ (abs_le.mp (hcoord i)).1, fun i ↦ (abs_le.mp (hcoord i)).2⟩
  have hp : volume (Metric.ball (0 : E) 1) ≤ volume (e ⁻¹' U) := measure_mono hsub
  rw [hvol] at hp
  have ht := ENNReal.toReal_mono (by finiteness) hp
  simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using ht

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- The bounded algebraic integers are embedded injectively into the
Euclidean lattice and counted by finite-volume packing. -/
private theorem boundedArchimedeanIntegers_count_of_short_basis
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hnorm : ∀ i, ‖b i‖ ≤ M) :
    ((boundedArchimedeanIntegers K B).ncard : ℝ) *
        ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ≤
      (2 : ℝ) ^ Module.finrank ℚ K *
        (2 * Real.sqrt (Module.finrank ℚ K) * B + Module.finrank ℚ K * M) ^
          Module.finrank ℚ K := by
  classical
  let := Fintype.ofFinite ι
  let e : 𝓞 K → mixedEmbedding.euclidean.integerLattice K :=
    fun x ↦ ⟨euclideanNumberFieldEmbedding K (x : K),
      euclideanNumberFieldEmbedding_mem_integerLattice K x⟩
  have he : Function.Injective e := by
    intro x y h
    exact RingOfIntegers.coe_injective
      (euclideanNumberFieldEmbedding_injective K (congrArg Subtype.val h))
  let s := (boundedArchimedeanIntegers_finite K B).toFinset.image e
  have hs : ∀ x ∈ s, ‖(x : mixedEmbedding.euclidean.mixedSpace K)‖ ≤
      Real.sqrt (Module.finrank ℚ K) * B := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact euclideanNumberFieldEmbedding_norm_le K hB (z : K)
      ((boundedArchimedeanIntegers_finite K B).mem_toFinset.mp hz)
  have hcard : s.card = (boundedArchimedeanIntegers K B).ncard := by
    rw [Finset.card_image_of_injective _ he]
    exact Set.ncard_eq_toFinset_card _ (boundedArchimedeanIntegers_finite K B) |>.symm
  have hp := superlattice_finite_packing_polynomial b
    (mixedEmbedding.euclidean.integerLattice K) hb s
    (mul_nonneg (Real.sqrt_nonneg _) hB) hM hs hnorm
  rw [hcard, euclidean_integerLattice_covolume, mixedEmbedding.euclidean.finrank] at hp
  have hdim : Fintype.card ι = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_basis b, mixedEmbedding.euclidean.finrank]
  rw [hdim] at hp
  have hunit : volume.real (Metric.ball (0 : mixedEmbedding.euclidean.mixedSpace K) 1) ≤
      (2 : ℝ) ^ Module.finrank ℚ K := by
    simpa only [mixedEmbedding.euclidean.finrank] using
      (unitBall_volume_le_two_pow_finrank
        (E := mixedEmbedding.euclidean.mixedSpace K))
  have hR : 0 ≤ 2 * (Real.sqrt (Module.finrank ℚ K) * B) +
      (Module.finrank ℚ K : ℝ) * M := by positivity
  calc
    _ ≤ _ := hp
    _ ≤ _ := (mul_le_mul_of_nonneg_left hunit (pow_nonneg hR _)).trans_eq (by ring)

/-- A dimension-only coefficient for the box count when the independent
integral vectors have norm at most `C` times the box radius. -/
def numberFieldLatticeBoxConstant (n : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 * Real.sqrt n + n * C) ^ n

/-- The box-count constant `numberFieldLatticeBoxConstant n C` is nonnegative for `C ≥ 0`. -/
lemma numberFieldLatticeBoxConstant_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ numberFieldLatticeBoxConstant n C := by
  unfold numberFieldLatticeBoxConstant
  positivity

open Classical in
private theorem boundedArchimedeanIntegers_count_of_relative_short_basis
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hnorm : ∀ i, ‖b i‖ ≤ C * B) :
    ((boundedArchimedeanIntegers K B).ncard : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      numberFieldLatticeBoxConstant (Module.finrank ℚ K) C * B ^ Module.finrank ℚ K := by
  classical
  let := Fintype.ofFinite ι
  have hp := boundedArchimedeanIntegers_count_of_short_basis K b hb hB
    (mul_nonneg hC hB) hnorm
  have hr : nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have := card_add_two_mul_card_eq_rank K
    omega
  have hpow : (2 : ℝ)⁻¹ ^ Module.finrank ℚ K ≤ (2 : ℝ)⁻¹ ^ nrComplexPlaces K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
  have hc := mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg |(discr K : ℝ)|)
  have hs := (mul_le_mul_of_nonneg_left hc
    (Nat.cast_nonneg (boundedArchimedeanIntegers K B).ncard)).trans hp
  have he :
      ((boundedArchimedeanIntegers K B).ncard : ℝ) *
          ((2 : ℝ)⁻¹ ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)|) =
        (((boundedArchimedeanIntegers K B).ncard : ℝ) * Real.sqrt |(discr K : ℝ)|) /
          (2 : ℝ) ^ Module.finrank ℚ K := by
    rw [inv_pow, div_eq_mul_inv]
    ring
  rw [he] at hs
  have ht := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mp hs
  have hrad : 2 * Real.sqrt (Module.finrank ℚ K) * B +
      (Module.finrank ℚ K : ℝ) * (C * B) =
      (2 * Real.sqrt (Module.finrank ℚ K) + Module.finrank ℚ K * C) * B := by ring
  rw [hrad, mul_pow] at ht
  exact ht.trans_eq (by unfold numberFieldLatticeBoxConstant; ring)

open Classical in
/-- Dividing by short integer translates gives the expected
one-dimensional saving for translation classes. -/
theorem boundedSquareNormTranslationClasses_count_of_relative_short_basis
    {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hnorm : ∀ i, ‖b i‖ ≤ C * B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) *
        Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) C *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  classical
  let := Fintype.ofFinite ι
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hp := boundedSquareNormTranslationClasses_packing K B B
  have hpR :
      ((boundedSquareNormTranslationClasses K B).card : ℝ) *
          ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤
        (boundedArchimedeanIntegers K (2 * B)).ncard := by
    exact_mod_cast (by simpa only [two_mul] using hp)
  have hfloor : (0 : ℤ) ≤ 2 * ⌊B⌋ + 1 := by
    have hh : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.mpr hBpos.le
    omega
  have htranslates : B ≤ ((2 * ⌊B⌋ + 1).toNat : ℝ) := by
    have hc : ((2 * ⌊B⌋ + 1).toNat : ℝ) = ((2 * ⌊B⌋ + 1 : ℤ) : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hfloor)
    rw [hc]
    push_cast
    have hh := Int.lt_floor_add_one B
    linarith
  have hcard := (mul_le_mul_of_nonneg_left htranslates
    (Nat.cast_nonneg (boundedSquareNormTranslationClasses K B).card)).trans hpR
  have hcount := boundedArchimedeanIntegers_count_of_relative_short_basis K b hb
    (B := 2 * B) (by positivity) hC (fun i ↦ (hnorm i).trans (by
      nlinarith [mul_nonneg hC hBpos.le]))
  have hh := (mul_le_mul_of_nonneg_right hcard
    (Real.sqrt_nonneg |(discr K : ℝ)|)).trans hcount
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hpow : B ^ Module.finrank ℚ K = B ^ (Module.finrank ℚ K - 1) * B := by
    rw [← pow_succ]
    congr 1
    omega
  rw [mul_pow, hpow] at hh
  apply (mul_le_mul_iff_left₀ hBpos).mp
  nlinarith only [hh]

end
end CCDN
