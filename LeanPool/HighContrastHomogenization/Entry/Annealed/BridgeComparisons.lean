/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.BridgeSourceTail
public import LeanPool.HighContrastHomogenization.Entry.TwoGridWhitney
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization: Entry.Annealed.BridgeComparisons

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The common partition comparison

`p.successful.short.bridge`. Countable subadditivity uses response
quadratics on the open parent and its open cells. A single locally elliptic
representative serves the entire partition. The null remainder is never
an argument of `coarseBlock`. This file assembles `bridge_partition_comparison`,
the shared machinery behind the two one-sided Whitney comparisons, which
`BridgeComparisonsOneSided` carries as `bridge_upper_comparison` and
`bridge_lower_comparison`.

The supporting estimates are inherited through `BridgeSourceTail`.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockScale blockSub blockVecDot_blockMatVecMul_eq_sum
  coarseBlock)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Filter
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- Quadratic evaluation distributes over a finite sum of full blocks. -/
theorem bridge_quadratic_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (∑ i ∈ s, F i)) v) =
      ∑ i ∈ s, (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (F i)) v) := by
  classical
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := s)]

private theorem bridge_quadratic_nonneg {d : ℕ} {A : BlockMat d}
    (hA : Book.Ch02.BlockPosDef A) (v : BlockVec d) :
    0 ≤ (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v) := by
  by_cases hv : v = 0
  · simp [hv, blockVecDot, vecDot]
  · exact mul_nonneg (by norm_num) (hA v hv).le

private theorem bridge_integrable_quadratic {d : ℕ} {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → BlockMat d}
    (hA : ∀ α β, Integrable (fun a => blockMatEntry (A a) α β) P) (v : BlockVec d) :
    Integrable (fun a => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A a) v)) P := by
  simp only [blockVecDot_blockMatVecMul_eq_sum]
  apply Integrable.const_mul
  exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    ((hA α β).mul_const _).const_mul _

private theorem bridge_integral_quadratic {d : ℕ} {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → BlockMat d}
    (hA : ∀ α β, Integrable (fun a => blockMatEntry (A a) α β) P) (v : BlockVec d) :
    (∫ a, (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A a) v) ∂P) =
      (1 / 2 : ℝ) * blockVecDot v
        (blockMatVecMul (ofFullBlockMat (Matrix.of fun α β =>
          ∫ a, blockMatEntry (A a) α β ∂P)) v) := by
  rw [integral_const_mul]
  congr 1
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.of_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro α _
    rw [integral_finsetSum]
    · simp only [integral_const_mul, integral_mul_const]
    · exact fun β _ => ((hA α β).mul_const _).const_mul _
  · intro α _
    exact integrable_finsetSum _ fun β _ => ((hA α β).mul_const _).const_mul _

private theorem bridge_integrable_nonneg_series {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {P : Measure α} (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) P)
    (hf0 : ∀ i a, 0 ≤ f i a) (hs : ∀ a, Summable (fun i => f i a))
    (hE : Summable (fun i => ∫ a, f i a ∂P)) :
    Integrable (fun a => ∑' i, f i a) P := by
  classical
  refine ⟨?_, ?_⟩
  · apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (fun s => s.aestronglyMeasurable_fun_sum (fun i _ => (hf i).1))
    exact ae_of_all _ (fun a => (hs a).hasSum)
  · apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun a => tsum_nonneg (fun i => hf0 i a)))).2
    have he (a) : ENNReal.ofReal (∑' i, f i a) = ∑' i, ENNReal.ofReal (f i a) :=
      ENNReal.ofReal_tsum_of_nonneg (fun i => hf0 i a) (hs a)
    simp_rw [he]
    rw [lintegral_tsum (fun i => ((hf i).aestronglyMeasurable.aemeasurable).ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hf _) (ae_of_all _ (hf0 _))]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (hf0 i)) hE]
    exact ENNReal.ofReal_lt_top

/-- A countable adapted partition inherits every finite upper bound on its
annealed weighted sums. Positivity and bounded finite expected quadratics justify
summation under expectation; qualitative ellipticity is only used pathwise. -/
theorem bridge_annealed_partition_bound {d : ℕ} [NeZero d]
    {ι : Type*} {s : Set ι} (hs : s.Countable)
    (P : Measure (CoeffSpace d)) (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (qi : ι → Mat d) (hqi : ∀ i ∈ s, IsUnit (qi i)) (ji : ι → ℤ) (yi : ι → Vec d)
    (B : BlockMat d) :
    let W := adaptedCellTranslate q j y
    let U := fun i => adaptedCellTranslate (qi i) (ji i) (yi i)
    (∀ i ∈ s, U i ⊆ W) → s.PairwiseDisjoint U →
      volume (W \ ⋃ i ∈ s, U i) = 0 →
      HasIntegrableCoarseBlock P W → (∀ i ∈ s, HasIntegrableCoarseBlock P (U i)) →
      (∀ F : Finset s, BlockMatLoewnerLE
        (ofFullBlockMat (∑ i ∈ F, ((volume (U i)).toReal / (volume W).toReal) •
          toFullBlockMat (annealedBlock P (U i)))) B) →
      BlockMatLoewnerLE (annealedBlock P W) B := by
  intro W U hsub hdis hnull hWint hUint hfin v
  classical
  let : Countable s := hs.to_subtype
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q j y
  let : IsFiniteMeasure (volumeMeasureOn W) :=
    ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hWvol : (volume W).toReal ≠ 0 := by
    dsimp [W]
    rw [volume_adaptedCellTranslate_toReal]
    have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
    positivity
  let w := fun i : s => (volume (U i)).toReal / (volume W).toReal
  let f := fun (i : s) a => w i * ((1 / 2 : ℝ) *
    blockVecDot v (blockMatVecMul (coarseBlock (U i) a) v))
  have hw0 (i : s) : 0 ≤ w i := by dsimp [w]; positivity
  have hopen (i) (hi : i ∈ s) : IsOpen (U i) :=
    isOpen_adaptedCellTranslate (hqi i hi) (ji i) (yi i)
  have hw : Summable w := summable_volumeRatio (fun i hi => (hopen i hi).measurableSet) hsub hdis
  have hwt : (∑' i, w i) = 1 := Source.tsum_volumeRatio_eq_one hs hWvol
    (fun i hi => (hopen i hi).measurableSet) hsub hdis hnull
  have hf0 (i : s) (a) : 0 ≤ f i a := mul_nonneg (hw0 i)
    (bridge_quadratic_nonneg (blockPosDef_coarseBlock_adapted (qi i)
      (hqi i i.2) (ji i) (yi i) a) v)
  have hf (i : s) : Integrable (f i) P :=
    (bridge_integrable_quadratic (hUint i i.2) v).const_mul _
  have hEf (i : s) : (∫ a, f i a ∂P) = w i * ((1 / 2 : ℝ) *
      blockVecDot v (blockMatVecMul (annealedBlock P (U i)) v)) := by
    dsimp [f]
    rw [integral_const_mul, bridge_integral_quadratic (hUint i i.2)]
    rfl
  have hEfin (F : Finset s) : (∑ i ∈ F, ∫ a, f i a ∂P) ≤
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul B v) := by
    have h := hfin F v
    rw [bridge_quadratic_sum] at h
    simp only [hEf]
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    exact (Source.quadratic_blockScale (w i) (annealedBlock P (U i)) v).symm
  have hE : Summable (fun i => ∫ a, f i a ∂P) :=
    summable_of_sum_le (fun i => integral_nonneg (hf0 i)) hEfin
  have hpath (a) : Summable (fun i => f i a) ∧
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (coarseBlock W a) v) ≤ ∑' i, f i a := by
    obtain ⟨lam, Lam, g, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_adapted q hq j y a
    let b := vecDot (-v.1) v.2
    have heq (i : s) : w i * ResponseJ (U i) (-v.1) v.2 g = f i a - w i * b := by
      rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae),
        responseJ_eq_coarseBlock_adapted (qi i) (hqi i i.2) (ji i) (yi i) a]
      simp only [neg_neg, Prod.mk.eta]
      dsimp [f, b]
      ring
    have hr := summable_volumeWeightedResponseJ
      hs hopen hsub hdis hEll (-v.1) v.2
    have hfs : Summable (fun i => f i a) := by
      have h := hr.add (hw.mul_right b)
      convert h using 1
      funext i
      rw [heq]
      ring
    refine ⟨hfs, ?_⟩
    have hp := Source.responseJ_le_tsum_of_partition hs
      (isOpen_adaptedCellTranslate hq j y) hWvol hopen hsub hdis hnull hEll (-v.1) v.2
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae),
      responseJ_eq_coarseBlock_adapted q hq j y a] at hp
    simp only [neg_neg, Prod.mk.eta] at hp
    have ht : (∑' i : s, w i * ResponseJ (U i) (-v.1) v.2 g) = (∑' i, f i a) - b := by
      simp_rw [heq]
      rw [hfs.tsum_sub (hw.mul_right b), tsum_mul_right, hwt, one_mul]
    change _ ≤ ∑' i : s, w i * ResponseJ (U i) (-v.1) v.2 g at hp
    rw [ht] at hp
    exact sub_le_sub_iff_right b |>.mp hp
  have hts := bridge_integrable_nonneg_series f hf hf0 (fun a => (hpath a).1) hE
  have hEnorm : Summable (fun i => ∫ a, ‖f i a‖ ∂P) := by
    simpa only [Real.norm_of_nonneg (hf0 _ _)] using hE
  have hp := integral_mono_ae (bridge_integrable_quadratic hWint v) hts
    (ae_of_all _ (fun a => (hpath a).2))
  rw [bridge_integral_quadratic hWint,
    ← integral_tsum_of_summable_integral_norm hf hEnorm] at hp
  exact hp.trans (hE.tsum_le_of_sum_le hEfin)

/-- The finite center-row mass is the mass of the corresponding
fiber of the pair index. This preserves the inclusive reverse cap row. -/
theorem bridge_maximal_row_mass {d : ℕ}
    (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q) (cap t : ℤ)
    (hfin : (maximalAdaptedCellCenters W q cap t).Finite) (V : ℝ) :
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    Summable (fun i : {i : I // i.1.1 = t} =>
      (volume (adaptedCellAtCenter q i.1.1.1 i.1.1.2)).toReal / V) ∧
    (∑' i : {i : I // i.1.1 = t},
      (volume (adaptedCellAtCenter q i.1.1.1 i.1.1.2)).toReal / V) =
      ∑ _z ∈ hfin.toFinset, (volume (adaptedCell q t)).toReal / V := by
  intro I
  classical
  let hI : (maximalAdaptedCellIndices W q cap t).Finite :=
    hfin.of_finite_image (adaptedCellCenter_injective q t hq).injOn
  let e : {i : I // i.1.1 = t} ≃ maximalAdaptedCellIndices W q cap t :=
    { toFun := fun i => ⟨i.1.1.2, by have h := i.1.2; rwa [i.2] at h⟩
      invFun := fun w => ⟨⟨(t, w), w.2⟩, rfl⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext i.2.symm rfl
      right_inv := fun _ => rfl }
  let := hI.fintype
  constructor
  · exact e.symm.summable_iff.mp (hasSum_fintype _).summable
  · have he := e.symm.tsum_eq (fun i : {i : I // i.1.1 = t} =>
      (volume (adaptedCellAtCenter q i.1.1.1 i.1.1.2)).toReal / V)
    rw [← he]
    change (∑' w : maximalAdaptedCellIndices W q cap t,
      (volume (adaptedCellAtCenter q t w)).toReal / V) = _
    simp only [volume_adaptedCellAtCenter, ← volume_adaptedCell,
      tsum_fintype, Finset.sum_const, nsmul_eq_mul]
    have hcard : hfin.toFinset.card = Fintype.card (maximalAdaptedCellIndices W q cap t) := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, maximalAdaptedCellCenters_eq_image_indices,
        Set.ncard_image_of_injective _ (adaptedCellCenter_injective q t hq)]
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    rw [hcard]
    rfl

private theorem bridge_finite_row_bound {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (J cap j : ℤ) (C : ℝ)
    (hrow : ∀ t ∈ Finset.Icc J cap, (∑' i : {i // r i = t}, w i) ≤
      C * (3 : ℝ) ^ ((t : ℝ) - j)) (b : ℤ → ℝ)
    (hb : ∀ t ∈ Finset.Icc J cap, 0 ≤ b t) (F : Finset ι)
    (hF : ∀ i ∈ F, r i ∈ Finset.Icc J cap) :
    (∑ i ∈ F, w i * b (r i)) ≤ C * ∑ t ∈ Finset.Icc J cap,
      (3 : ℝ) ^ ((t : ℝ) - j) * b t := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hF (fun i => w i * b (r i)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have he : (∑ i ∈ F with r i = t, w i * b (r i)) =
      (∑ i ∈ F with r i = t, w i) * b t := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
  rw [he]
  have hwt : Summable (fun i : {i // r i = t} => w i) := hw.subtype _
  have hs := hwt.sum_le_tsum
    (F.subtype (fun i => r i = t)) (fun i _ => hw0 i)
  rw [Finset.sum_subtype_eq_sum_filter] at hs
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hs.trans (hrow t ht)) (hb t ht)

private theorem bridge_finite_mean_le_series {d : ℕ} {ι : Type*}
    (P : Measure (CoeffSpace d)) (A : ι → CoeffSpace d → BlockMat d)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpos : ∀ i a, Book.Ch02.BlockPosDef (A i a))
    (hAi : ∀ i α β, Integrable (fun a => blockMatEntry (A i a) α β) P)
    (hseries : ∀ᵐ a ∂P, Summable (fun i => w i • toFullBlockMat (A i a)))
    (hM : ∀ α β, Integrable (fun a => blockMatEntry
      (ofFullBlockMat (∑' i, w i • toFullBlockMat (A i a))) α β) P)
    (F : Finset ι) :
    BlockMatLoewnerLE
      (ofFullBlockMat (∑ i ∈ F, w i • toFullBlockMat
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (A i a) α β ∂P))))
      (ofFullBlockMat (Matrix.of fun α β => ∫ a,
        blockMatEntry (ofFullBlockMat (∑' i, w i • toFullBlockMat (A i a))) α β ∂P)) := by
  intro v
  rw [bridge_quadratic_sum]
  have hterm (i : ι) : (1 / 2 : ℝ) * blockVecDot v
      (blockMatVecMul (ofFullBlockMat (w i • toFullBlockMat
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (A i a) α β ∂P)))) v) =
      ∫ a, w i * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A i a) v)) ∂P := by
    rw [integral_const_mul, bridge_integral_quadratic (hAi i)]
    exact Source.quadratic_blockScale _ _ _
  simp_rw [hterm]
  rw [← integral_finsetSum F (fun i _ => (bridge_integrable_quadratic (hAi i) v).const_mul _),
    ← bridge_integral_quadratic hM]
  apply integral_mono_ae
    (integrable_finsetSum F (fun i _ => (bridge_integrable_quadratic (hAi i) v).const_mul _))
    (bridge_integrable_quadratic hM v)
  filter_upwards [hseries] with a ha
  rw [Source.quadratic_tsum_fullBlock _ ha]
  have he (i : ι) : (1 / 2 : ℝ) * blockVecDot v
      (blockMatVecMul (ofFullBlockMat (w i • toFullBlockMat (A i a))) v) =
      w i * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A i a) v)) :=
    Source.quadratic_blockScale _ _ _
  have hs := Source.summable_quadratic_fullBlock _ ha v
  simp_rw [he] at hs ⊢
  exact hs.sum_le_tsum F (fun i _ => mul_nonneg (hw i) (bridge_quadratic_nonneg (hpos i a) v))

private theorem bridge_split_weighted_sum {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (old : ι → Prop)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hwt : (∑' i, w i) ≤ 1)
    (J cap j : ℤ) (C : ℝ) (hcap : ∀ i, old i → r i ≤ cap)
    (hrow : ∀ t ∈ Finset.Icc J cap,
      (∑' i : {i : {i // old i} // r i = t}, w i.1) ≤ C * (3 : ℝ) ^ ((t : ℝ) - j))
    (g : ι → ℝ) (b : ℤ → ℝ) (base tail : ℝ)
    (hbase0 : 0 ≤ base) (hb : ∀ t ∈ Finset.Icc J cap, 0 ≤ b t)
    (hbase : ∀ i, ¬old i → g i = base)
    (hmid : ∀ i, old i → J ≤ r i → g i = b (r i))
    (hfine : ∀ F : Finset {i : {i // old i} // r i < J},
      (∑ i ∈ F, w i.1 * g i.1) ≤ tail) (F : Finset ι) :
    (∑ i ∈ F, w i * g i) ≤ base + C *
      (∑ t ∈ Finset.Icc J cap, (3 : ℝ) ^ ((t : ℝ) - j) * b t) + tail := by
  classical
  let O := {i // old i}
  let FO := F.subtype old
  have hold : (∑ i ∈ F with old i, w i * g i) ≤
      C * (∑ t ∈ Finset.Icc J cap, (3 : ℝ) ^ ((t : ℝ) - j) * b t) + tail := by
    rw [← Finset.sum_subtype_eq_sum_filter]
    change (∑ i ∈ FO, w i * g i) ≤ _
    have hlow := hfine (FO.subtype (fun i : O => r i < J))
    rw [Finset.sum_subtype_eq_sum_filter (fun i : O => w i * g i)] at hlow
    have hhigh := bridge_finite_row_bound (fun i : O => w i) (fun i => r i)
      (fun i => hw0 i) (hw.subtype old) J cap j C hrow b hb
      (FO.filter (fun i => ¬r i < J)) (fun i hi =>
        Finset.mem_Icc.mpr ⟨by change J ≤ r i; have := (Finset.mem_filter.mp hi).2; omega, hcap
          i i.2⟩)
    have hheq : (∑ i ∈ FO with ¬r (i : O) < J, w i * g i) =
        ∑ i ∈ FO with ¬r (i : O) < J, w i * b (r i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmid i i.2 (by have := (Finset.mem_filter.mp hi).2; omega)]
    have hsplit := Finset.sum_filter_add_sum_filter_not FO (fun i => r i < J)
      (fun i => w i * g i)
    linarith only [hlow, hhigh, hheq, hsplit]
  have hbaseF : (∑ i ∈ F with ¬old i, w i * g i) ≤ base := by
    have he : (∑ i ∈ F with ¬old i, w i * g i) = (∑ i ∈ F with ¬old i, w i) * base := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i hi => by rw [hbase i (Finset.mem_filter.mp hi).2])
    rw [he]
    exact mul_le_of_le_one_left hbase0 ((hw.sum_le_tsum _ (fun i _ => hw0 i)).trans hwt)
  have hsplit := Finset.sum_filter_add_sum_filter_not F old (fun i => w i * g i)
  linarith only [hold, hbaseF, hsplit]

private theorem bridge_quadratic_smul {d : ℕ} (c : ℝ) (A : BlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (c • toFullBlockMat A)) v) =
      c * ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul A v)) :=
  Source.quadratic_blockScale c A v

private theorem bridge_quadratic_add {d : ℕ} (M N : FullBlockMat d) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (M + N)) v) =
      (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v) +
        (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat N) v) := by
  simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
    Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

/-- The common partition comparison, before harmless enlargement of its fine
coefficient. The old-grid normalization is obtained inside the proof;
all constants precede the law. The two constructions discharge the
geometric premises separately below. -/
theorem bridge_partition_comparison (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ (m mBase mParent : Mat d), m.PosDef → mBase.PosDef → mParent.PosDef →
          ∀ cap b j terminal : ℤ, (jStar : ℤ) ≤ cap → (jStar : ℤ) ≤ b →
            (jStar : ℤ) ≤ terminal →
            adaptedCell (explicitRoundedGrid jStar mParent) j ⊆ centeredCube d (2 * (jStar : ℤ)) →
            adaptedCell (explicitRoundedGrid jStar m) terminal ⊆ centeredCube d (2 * (jStar : ℤ)) →
            ∀ (ι : Type) [Countable ι] (I : Set ι) (qi : ι → Mat d),
              (∀ i ∈ I, IsUnit (qi i)) → ∀ (ji : ι → ℤ) (yi : ι → Vec d)
                (old : ι → Prop) (r : ι → ℤ) (z : ι → Fin d → ℤ),
              let W := adaptedCell (explicitRoundedGrid jStar mParent) j
              let U := fun i => adaptedCellTranslate (qi i) (ji i) (yi i)
              (∀ i ∈ I, U i ⊆ W) → I.PairwiseDisjoint U → volume (W \ ⋃ i ∈ I, U i) = 0 →
              (∀ i ∈ I, old i → U i = adaptedCellAtCenter (explicitRoundedGrid jStar m) (r i) (z
                i)) →
              (∀ i ∈ I, ¬old i → U i = adaptedCellAtCenter (explicitRoundedGrid jStar mBase) b
                (z i)) →
              (∀ i ∈ I, old i → r i ≤ cap) →
              ∀ Cw : ℝ, 0 ≤ Cw →
                (∀ t : ℤ, t ≤ cap →
                  (∑' i : {i : {i : I // old i} // r i.1 = t},
                    (volume (U i.1.1)).toReal / (volume W).toReal) ≤
                    Cw * (3 : ℝ) ^ ((t : ℝ) - j)) →
                BlockMatLoewnerLE
                  (blockSub (adaptedMean P (explicitRoundedGrid jStar mParent) j)
                    (adaptedMean P (explicitRoundedGrid jStar mBase) b))
                  (ofFullBlockMat
                    (toFullBlockMat (blockScale Cw (ofFullBlockMat
                      (∑ t ∈ Finset.Icc (jStar : ℤ) cap, (3 : ℝ) ^ ((t : ℝ) - j) •
                        toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) t)))) +
                      toFullBlockMat (blockScale (C * Cw * aspectRatio E *
                        (Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - jStar)))
                        (adaptedMean P (explicitRoundedGrid jStar m) terminal)))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cs, Ca, hCs, hCa, hsource⟩ := bridge_fine_source_tail d hd γ hγ
  obtain ⟨Cn, Cb, hCn, hCb, hnorm⟩ := bridge_normalize_source_tail d hd γ hγ
  refine ⟨max Cs Cn, 2 * Ca * Cb, hCs.trans_le (le_max_left _ _), by positivity, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m mBase mParent hm hmBase hmParent
    cap b j terminal hcapJ hbJ htJ hWcube hTcube ι hι I qi hqi ji yi old r z
    W U hsub hdis hnull hold hbase hcap Cw hCw hrow
  classical
  have hlog : 0 ≤ Real.logb 3 (2 * K) := (Real.logb_pos (by norm_num)
    (by linarith only [hdag.one_lt_growthWitness] : (1 : ℝ) < 2 * K)).le
  have hsrcs := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left Cs Cn) hlog)).trans hsrc
  have hsrcn := (Int.ceil_mono (mul_le_mul_of_nonneg_right (le_max_right Cs Cn) hlog)).trans hsrc
  obtain ⟨X, _hX0, _hX, _hXi, _hEX, hfine⟩ := hsource P E Ψ K S hstat hdag jStar hj hsrcs
  let O := {i : I // old i}
  let F := {i : O // r i.1 < (jStar : ℤ)}
  let w := fun i : I => (volume (U i)).toReal / (volume W).toReal
  let A := fun i : I => annealedBlock P (U i)
  let M := fun a => ofFullBlockMat (∑' i : F, w i.1.1 • toFullBlockMat
    (coarseBlock (adaptedCellAtCenter (explicitRoundedGrid jStar m) (r i.1.1) (z i.1.1)) a))
  let T := blockScale ((2 * Ca * Cb) * Cw * aspectRatio E *
    (Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - jStar)))
    (adaptedMean P (explicitRoundedGrid jStar m) terminal)
  let B := blockScale Cw (ofFullBlockMat (∑ t ∈ Finset.Icc (jStar : ℤ) cap,
    (3 : ℝ) ^ ((t : ℝ) - j) • toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar m) t)))
  have hWp : W = adaptedCellTranslate (explicitRoundedGrid jStar mParent) j 0 := by
    simp only [W, adaptedCellTranslate, zero_add, Set.image_id']
  have hWfin : volume W ≠ ⊤ := hWp ▸ Transport.volume_adaptedCellTranslate_ne_top _ _ _
  let : IsFiniteMeasure (volumeMeasureOn W) :=
    ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hw0 (i : I) : 0 ≤ w i := by dsimp [w]; positivity
  have hw : Summable w := summable_volumeRatio
    (fun i hi => (isOpen_adaptedCellTranslate (hqi i hi) (ji i) (yi i)).measurableSet) hsub hdis
  have hwO : Summable (fun i : O => w i) := hw.subtype _
  have hwF : Summable (fun i : F => w i.1.1) := hwO.subtype _
  have hrowF (t : ℤ) : (∑' i : {i : F // r i.1.1 = t}, w i.1.1.1) ≤
      Cw * (3 : ℝ) ^ ((t : ℝ) - j) := by
    by_cases ht : t < (jStar : ℤ)
    · let e : {i : F // r i.1.1 = t} → {i : O // r i.1 = t} := fun i => ⟨i.1.1, i.2⟩
      have he : Function.Injective e := by
        intro i k h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : {i : O // r i.1 = t} => x.1) h
      have hle := Summable.tsum_le_tsum_of_inj e he (fun i _ => hw0 i.1)
        (fun _ => le_rfl) (hwF.subtype _) (hwO.subtype _)
      exact hle.trans (hrow t (ht.le.trans hcapJ))
    · have hempty : IsEmpty {i : F // r i.1.1 = t} := ⟨fun i => by
        have hi := i.1.2
        have he := i.2
        exact ht (he ▸ hi)⟩
      simp only [tsum_empty]
      exact mul_nonneg hCw (Real.rpow_nonneg (by norm_num) _)
  have hcF (i : F) : adaptedCellAtCenter (explicitRoundedGrid jStar m) (r i.1.1) (z i.1.1) ⊆ W := by
    rw [← hold i.1.1 i.1.1.2 i.1.2]
    exact hsub i.1.1 i.1.1.2
  have htail := hfine m hm W hWcube F (fun i => r i.1.1)
    (fun i => adaptedCellCenter (explicitRoundedGrid jStar m) (r i.1.1) (z i.1.1))
    (fun i => w i.1.1) (fun i => i.2) (fun i => hw0 i.1.1) hwF hcF j Cw hCw hrowF
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast (Multiscale.bigQ_two_le d γ hγ).trans' (by norm_num)
  have hM : ∀ α β, Integrable (fun a => blockMatEntry (M a) α β) P :=
    htail.1.integrable_entry hQ
  have hT : BlockMatLoewnerLE
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (M a) α β ∂P)) T := by
    have h := hnorm P E Ψ K S hstat hdag jStar hj hsrcn m hm terminal htJ hTcube
      _ _ (by positivity) htail.2.2
    convert h using 1 <;> try rfl
    change blockScale ((2 * Ca * Cb) * Cw * aspectRatio E *
        (Real.sqrt (‖m‖ * ‖m⁻¹‖)) ^ 2 * (3 : ℝ) ^ (-((j : ℝ) - jStar)))
        (adaptedMean P (explicitRoundedGrid jStar m) terminal) = _
    congr 1
    ring
  have hAi (i : I) : HasIntegrableCoarseBlock P (U i) := by
    by_cases hi : old i
    · rw [hold i i.2 hi]
      exact hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hj m hm _ _
    · rw [hbase i i.2 hi]
      exact hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hj mBase hmBase _ _
  have hWint : HasIntegrableCoarseBlock P W := by
    rw [hWp]
    exact hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      jStar hj mParent hmParent _ _
  have hquad0 (m₁ : Mat d) (hm₁ : m₁.PosDef) (s : ℤ) (v : BlockVec d) :
      0 ≤ (1 / 2 : ℝ) * blockVecDot v
        (blockMatVecMul (adaptedMean P (explicitRoundedGrid jStar m₁) s) v) := by
    have hi := hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hj m₁ hm₁ s 0
    have h : 0 ≤ ∫ a, (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul
        (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m₁) s 0) a) v) ∂P :=
      integral_nonneg (fun a => bridge_quadratic_nonneg
        (blockPosDef_coarseBlock_adapted _ (isUnit_roundedGrid hj hm₁) s 0 a) v)
    rw [bridge_integral_quadratic hi] at h
    simpa only [adaptedMean, adaptedCellTranslate, zero_add, Set.image_id'] using! h
  have hParent : BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar mParent) j)
      (ofFullBlockMat (toFullBlockMat (adaptedMean P (explicitRoundedGrid jStar mBase) b) +
        toFullBlockMat B + toFullBlockMat T)) := by
    change BlockMatLoewnerLE (annealedBlock P W) _
    rw [hWp]
    apply bridge_annealed_partition_bound (Set.to_countable I) P
      (explicitRoundedGrid jStar mParent) (isUnit_roundedGrid hj hmParent) j 0 qi hqi ji yi
    · simpa only [← hWp] using hsub
    · exact hdis
    · simpa only [← hWp] using hnull
    · simpa only [← hWp] using hWint
    · exact fun i hi => hAi ⟨i, hi⟩
    · intro FF v
      rw [bridge_quadratic_sum]
      simp only [bridge_quadratic_add, ofFullBlockMat_toFullBlockMat]
      have hwt : (∑' i, w i) ≤ 1 := by
        have hWvol : (volume W).toReal ≠ 0 := by
          rw [hWp, volume_adaptedCellTranslate_toReal]
          have hdet := ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_roundedGrid hj
            hmParent)).ne_zero
          positivity
        exact le_of_eq (Source.tsum_volumeRatio_eq_one (Set.to_countable I) hWvol
          (fun i hi => (isOpen_adaptedCellTranslate (hqi i hi) _ _).measurableSet) hsub hdis hnull)
      have hf (FF : Finset F) : BlockMatLoewnerLE
          (ofFullBlockMat (∑ i ∈ FF, w i.1.1 • toFullBlockMat (A i.1.1))) T := by
        have h := bridge_finite_mean_le_series P
          (fun i : F => fun a => coarseBlock
            (adaptedCellAtCenter (explicitRoundedGrid jStar m) (r i.1.1) (z i.1.1)) a)
          (fun i => w i.1.1) (fun i => hw0 i.1.1)
          (fun i a => blockPosDef_coarseBlock_adapted _ (isUnit_roundedGrid hj hm) _ _ a)
          (fun _ => hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hj m hm _ _)
          (htail.2.1.mono (fun _ ha => ha.1)) hM FF
        have he (i : F) : A i.1.1 = annealedBlock P
            (adaptedCellAtCenter (explicitRoundedGrid jStar m) (r i.1.1) (z i.1.1)) := by
          dsimp [A]
          rw [hold i.1.1 i.1.1.2 i.1.2]
        simpa only [he] using! h.trans hT
      have hs := bridge_split_weighted_sum w (fun i : I => r i) (fun i => old i)
        hw0 hw hwt jStar cap j Cw (fun i hi => hcap i i.2 hi)
        (fun t ht => hrow t (Finset.mem_Icc.mp ht).2)
        (fun i => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (A i) v))
        (fun t => (1 / 2 : ℝ) * blockVecDot v
          (blockMatVecMul (adaptedMean P (explicitRoundedGrid jStar m) t) v))
        ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (adaptedMean P (explicitRoundedGrid jStar
          mBase) b) v))
        ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul T v))
        (hquad0 mBase hmBase b v) (fun t _ => hquad0 m hm t v)
        (fun i hi => by dsimp [A]; rw [hbase i i.2 hi,
          annealedBlock_adaptedCellAtCenter P hstat jStar hj mBase hmBase b hbJ])
        (fun i hi hri => by dsimp [A]; rw [hold i i.2 hi,
          annealedBlock_adaptedCellAtCenter P hstat jStar hj m hm (r i) hri])
        (fun FF => by
          have h := hf FF v
          rw [bridge_quadratic_sum] at h
          simpa only [bridge_quadratic_smul] using h) FF
      simpa only [B, Source.quadratic_blockScale, bridge_quadratic_sum, bridge_quadratic_smul,
        Finset.mul_sum, ← hWp, A, w, U] using hs
  intro v
  have h := hParent v
  simp only [bridge_quadratic_add, ofFullBlockMat_toFullBlockMat] at h
  change (1 / 2 : ℝ) * blockVecDot v
    (blockMatVecMul (blockSub (adaptedMean P (explicitRoundedGrid jStar mParent) j)
      (adaptedMean P (explicitRoundedGrid jStar mBase) b)) v) ≤
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (toFullBlockMat B +
      toFullBlockMat T)) v)
  rw [bridge_quadratic_add]
  have he := blockVecDot_blockMatVecMul_ofFullBlockMat_sub
    (adaptedMean P (explicitRoundedGrid jStar mParent) j)
    (adaptedMean P (explicitRoundedGrid jStar mBase) b) v
  change blockVecDot v (blockMatVecMul (blockSub _ _) v) = _ at he
  rw [he]
  simp only [ofFullBlockMat_toFullBlockMat]
  linarith only [h]

end
end HCPolySupport.HighContrast.Annealed
