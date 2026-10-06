/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.CG.Proofs.FiniteVolumeWeights
public import LeanPool.HighContrastHomogenization.Entry.CG.Proofs.ResponseFiniteDefect
public import LeanPool.HighContrastHomogenization.Entry.CG.Proofs.ResponseSummable
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedDomainLocality
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization: Entry.Source.CoarseSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Countable source subadditivity

Near `l.source.whitney`. The accepted finite response defect and summability
estimates give countable subadditivity after the relative volume weights have total
mass one. Parent and pieces use one locally elliptic representative throughout each
exhaustion. No coarse block is evaluated on a non-open remainder.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace blockMatEntry_blockScale blockScale blockSub
  blockTrace blockVecDot_blockMatVecMul_eq_sum coarseBlock toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Source
open scoped Matrix.Norms.L2Operator
open Set MeasureTheory Filter Geometry
noncomputable section

/-- Countable relative volume weights have total mass one when the pieces cover a.e. -/
theorem tsum_volumeRatio_eq_one {d : ℕ} {ι : Type*} {s : Set ι} (hs : s.Countable)
    {W : Set (Vec d)} {U : ι → Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    (hWvol : (volume W).toReal ≠ 0)
    (hmeas : ∀ i ∈ s, MeasurableSet (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0) :
    (∑' i : s, (volume (U i)).toReal / (volume W).toReal) = 1 := by
  let : Countable s := hs.to_subtype
  have hd : Pairwise (fun i j : s => Disjoint (U i) (U j)) := by
    intro i j hij
    exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  have hu : volume (⋃ i : s, U i) = volume W := by
    apply measure_eq_measure_of_null_sdiff (iUnion_subset fun i : s => hsub i i.2)
    simpa only [iUnion_subtype] using hnull
  have hsum : (∑' i : s, volume (U i)) = volume W :=
    (measure_iUnion hd (fun i => hmeas i i.2)).symm.trans hu
  rw [tsum_div_const, ← ENNReal.tsum_toReal_eq (fun i : s =>
    volume_piece_ne_top_of_subset (hsub i i.2)), hsum, div_self hWvol]

/-- Finite response defects vanish under an a.e. countable partition.
The fixed ellipticity constants serve the parent and every piece in this proof. -/
theorem responseJ_le_tsum_of_partition {d : ℕ} {ι : Type*} {s : Set ι} (hs : s.Countable)
    {W : Set (Vec d)} {U : ι → Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) (p q : Vec d) :
    ResponseJ W p q a ≤
      ∑' i : s, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a := by
  classical
  have hw := summable_volumeRatio (fun i hi => (hopen i hi).measurableSet) hsub hdisj
  have hwt := tsum_volumeRatio_eq_one hs hWvol (fun i hi => (hopen i hi).measurableSet)
    hsub hdisj hnull
  have hr := summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_provider
    hs hopen hsub hdisj hEll p q
  let C : ℝ := lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q)
  have hlim := Tendsto.add hr.hasSum
    (((show Tendsto (fun _ : Finset s => (1 : ℝ)) atTop (nhds 1) from tendsto_const_nhds).sub
      hw.hasSum).mul_const C)
  simp only [hwt, sub_self, zero_mul, add_zero] at hlim
  apply ge_of_tendsto' hlim
  intro F
  have hdF : (F : Set s).PairwiseDisjoint (fun i : s => U i) := by
    intro i _ j _ hij
    exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  have hwF := sum_volumeRatio_add_remainder_eq_one F hWvol
    (fun i _ => (hopen i i.2).measurableSet) (fun i _ => hsub i i.2) hdF
  have hrF := responseJ_le_sum_volumeRatio_mul_responseJ_add_defect_of_isEllipticFieldOn_provider
    F hWopen hWvol (fun i _ => hopen i i.2) (fun i _ => hsub i i.2) hdF hEll p q
  change ResponseJ W p q a ≤
    ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a +
      (1 - ∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal) * C
  dsimp [C]
  have heq : 1 - (∑ i ∈ F, (volume (U i)).toReal / (volume W).toReal) =
      (volume (W \ ⋃ i ∈ F, U i)).toReal / (volume W).toReal := by
    linarith only [hwF]
  rwa [heq]

/-- Scalar dilation acts on the entire doubled quadratic form. -/
theorem quadratic_blockScale {d : ℕ} (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X)) := by
  simp only [blockScale, blockMatVecMul, smul_matVecMul, ← smul_add,
    blockVecDot, vecDot_smul_right]
  ring

/-- The mixed response identities and total volume mass turn a countable response
partition into an every-vector block bound. This conditional bridge is discharged
by the adapted coarse-block mixed response identity on the actual cells; it asserts
no source estimate by itself. -/
theorem block_bound_of_response_partition {d : ℕ} {ι : Type*} {s : Set ι} (hs : s.Countable)
    {W : Set (Vec d)} {U : ι → Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (A E : BlockMat d) (Ai : ι → BlockMat d) (c : ι → ℝ)
    (hA : ∀ p q, ResponseJ W p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul A (-p, q)) - vecDot p q)
    (hAi : ∀ i ∈ s, ∀ p q, ResponseJ (U i) p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul (Ai i) (-p, q)) - vecDot p q)
    (hc : Summable (fun i : s => (volume (U i)).toReal / (volume W).toReal * c i))
    (hb : ∀ i ∈ s, BlockMatLoewnerLE (Ai i) (blockScale (c i) E)) :
    BlockMatLoewnerLE A
      (blockScale (∑' i : s, (volume (U i)).toReal / (volume W).toReal * c i) E) := by
  intro X
  let e : ℝ := (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul E X)
  let v : ℝ := vecDot (-X.1) X.2
  have hw := summable_volumeRatio (fun i hi => (hopen i hi).measurableSet) hsub hdisj
  have hwt := tsum_volumeRatio_eq_one hs hWvol (fun i hi => (hopen i hi).measurableSet)
    hsub hdisj hnull
  have hr := summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_provider
    hs hopen hsub hdisj hEll (-X.1) X.2
  have hUpper : Summable (fun i : s =>
      ((volume (U i)).toReal / (volume W).toReal * c i) * e -
        ((volume (U i)).toReal / (volume W).toReal) * v) :=
    (hc.mul_right e).sub (hw.mul_right v)
  have hle : (∑' i : s, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) (-X.1) X.2 a) ≤
      (∑' i : s, (((volume (U i)).toReal / (volume W).toReal * c i) * e -
        ((volume (U i)).toReal / (volume W).toReal) * v)) := by
    apply hr.tsum_le_tsum _ hUpper
    intro i
    have hbi := hb i i.2 X
    rw [quadratic_blockScale] at hbi
    rw [hAi i i.2]
    simp only [neg_neg, Prod.mk.eta]
    have hw0 : 0 ≤ (volume (U i)).toReal / (volume W).toReal := by positivity
    have ht := mul_le_mul_of_nonneg_left (sub_le_sub_right hbi v) hw0
    dsimp [e, v]
    nlinarith only [ht]
  rw [(hc.mul_right e).tsum_sub (hw.mul_right v), tsum_mul_right, tsum_mul_right, hwt, one_mul] at hle
  have hparent := responseJ_le_tsum_of_partition hs hWopen hWvol hopen hsub hdisj hnull hEll (-X.1) X.2
  rw [hA] at hparent
  simp only [neg_neg, Prod.mk.eta] at hparent
  rw [quadratic_blockScale]
  dsimp [e, v] at hle
  linarith only [hparent, hle]

/-- Countable subadditivity with a scalar reference bound, on the actual qualitative
coefficient carrier and invertible adapted cells. Every response identity is supplied
by the adapted coarse-block mixed response identity. -/
theorem coarseBlock_adapted_partition_bound {d : ℕ} [NeZero d]
    {ι : Type*} {s : Set ι} (hs : s.Countable)
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (qi : ι → Mat d) (hqi : ∀ i ∈ s, IsUnit (qi i)) (ji : ι → ℤ) (yi : ι → Vec d)
    (a : CoeffSpace d) (E : BlockMat d) (c : ι → ℝ) :
    let W := adaptedCellTranslate q j y
    let U := fun i => adaptedCellTranslate (qi i) (ji i) (yi i)
    (∀ i ∈ s, U i ⊆ W) → s.PairwiseDisjoint U →
      volume (W \ ⋃ i ∈ s, U i) = 0 →
      Summable (fun i : s => (volume (U i)).toReal / (volume W).toReal * c i) →
      (∀ i ∈ s, BlockMatLoewnerLE (coarseBlock (U i) a) (blockScale (c i) E)) →
      BlockMatLoewnerLE (coarseBlock W a)
        (blockScale (∑' i : s, (volume (U i)).toReal / (volume W).toReal * c i) E) := by
  intro W U hsub hdisj hnull hc hb
  have hWfin : volume W ≠ ⊤ := Transport.volume_adaptedCellTranslate_ne_top q j y
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hWpos : 0 < volume W := by
    dsimp [W]
    rw [volume_adaptedCellTranslate]
    have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet)).ne'
      (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) d).ne'
  have hWvol : (volume W).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hWpos.ne', hWfin⟩
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j y a
  apply block_bound_of_response_partition hs (isOpen_adaptedCellTranslate hq j y)
    hWvol (fun i hi => isOpen_adaptedCellTranslate (hqi i hi) (ji i) (yi i))
    hsub hdisj hnull hEll (coarseBlock W a) E (fun i => coarseBlock (U i) a) c _ _ hc hb
  · intro p r
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]
    exact Annealed.responseJ_eq_coarseBlock_adapted q hq j y a p r
  · intro i hi p r
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]
    exact Annealed.responseJ_eq_coarseBlock_adapted (qi i) (hqi i hi) (ji i) (yi i) a p r

/-- Scaling a positive reference block is monotone in the real scalar, in the full
quadratic order. -/
theorem blockScale_le_blockScale_of_pos {d : ℕ} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E) {c c' : ℝ} (hc : c ≤ c') :
    BlockMatLoewnerLE (blockScale c E) (blockScale c' E) := by
  intro v
  rw [quadratic_blockScale, quadratic_blockScale]
  have hv : 0 ≤ blockVecDot v (blockMatVecMul E v) := by
    by_cases hz : v = 0
    · simp [hz, blockVecDot, vecDot]
    · exact (hE v hz).le
  have hq : 0 ≤ (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul E v) :=
    mul_nonneg (by norm_num) hv
  exact mul_le_mul_of_nonneg_right hc hq

/-- Full block symmetry and positive quadratic form give the actual spectral
positive-semidefinite matrix used by the Schatten norm. -/
theorem fullBlock_posSemidef_of_pos {d : ℕ} {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hpos : Book.Ch02.BlockPosDef A) :
    (toFullBlockMat A).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨(Analysis.toFullBlockMat_isHermitian_iff A).2 hA, ?_⟩
  intro x
  have hnonneg : 0 ≤ blockVecDot (ofFullBlockVec x) (blockMatVecMul A (ofFullBlockVec x)) := by
    by_cases hzero : ofFullBlockVec x = 0
    · simp [hzero, blockVecDot, vecDot]
    · exact (hpos _ hzero).le
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec] at hnonneg
  simpa only [star_trivial] using hnonneg

/-- Full quadratic order bounds the trace without assuming entrywise order. -/
theorem blockTrace_le_of_order {d : ℕ} {A B : BlockMat d}
    (hAB : BlockMatLoewnerLE A B) : blockTrace A ≤ blockTrace B := by
  change (∑ α : BlockCoord d, toFullBlockMat A α α) ≤ ∑ α : BlockCoord d, toFullBlockMat B α α
  apply Finset.sum_le_sum
  intro α _
  have h := hAB (blockBasis α)
  rw [blockBasis_pairing, blockBasis_pairing] at h
  simp only [toFullBlockMat_eq_blockMatEntry]
  linarith only [h]

/-- Quadratic order on a positive full block controls its actual L2 operator norm. -/
theorem blockOpNorm_le_scale_trace {d : ℕ} {A E : BlockMat d} {c : ℝ}
    (hA : IsSymmetricBlockMat A) (hpos : Book.Ch02.BlockPosDef A)
    (horder : BlockMatLoewnerLE A (blockScale c E)) :
    blockOpNorm A ≤ c * blockTrace E := by
  have hpsd := fullBlock_posSemidef_of_pos hA hpos
  calc
    blockOpNorm A ≤ absSchattenNorm 1 A := Analysis.blockOpNorm_le_absSchattenNorm hpsd.isHermitian le_rfl
    _ ≤ blockTrace A := Analysis.absSchattenNorm_le_blockTrace hpsd le_rfl
    _ ≤ blockTrace (blockScale c E) := blockTrace_le_of_order horder
    _ = _ := by simp only [blockTrace, Matrix.trace, Matrix.diag,
      toFullBlockMat_eq_blockMatEntry, blockMatEntry_blockScale, Finset.mul_sum]

/-- A summable positive scalar order envelope makes the actual full matrix series
summable in the L2 operator topology. -/
theorem summable_fullBlock_of_order {d : ℕ} {ι : Type*}
    (A : ι → BlockMat d) (E : BlockMat d) (w c : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∀ i, IsSymmetricBlockMat (A i))
    (hp : ∀ i, Book.Ch02.BlockPosDef (A i))
    (ho : ∀ i, BlockMatLoewnerLE (A i) (blockScale (c i) E))
    (hc : Summable (fun i => w i * c i)) :
    Summable (fun i => w i • toFullBlockMat (A i)) := by
  apply (hc.mul_right (blockTrace E)).of_norm_bounded
  intro i
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
  calc
    _ ≤ w i * (c i * blockTrace E) := mul_le_mul_of_nonneg_left
      (blockOpNorm_le_scale_trace (hs i) (hp i) (ho i)) (hw i)
    _ = _ := by ring

/-- Every-vector quadratic evaluation commutes with a convergent full matrix
series; no replacement by scalar diagonal sums occurs. -/
theorem quadratic_tsum_fullBlock {d : ℕ} {ι : Type*}
    (F : ι → FullBlockMat d) (hF : Summable F) (v : BlockVec d) :
    (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (∑' i, F i)) v) =
      ∑' i, (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat (F i)) v) := by
  let L : FullBlockMat d →ₗ[ℝ] ℝ :=
    { toFun := fun M => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v)
      map_add' := by
        intro M N
        simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
          Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c M
        simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
          Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp only [mul_assoc, mul_left_comm (toFullBlockVec v _), ← Finset.mul_sum]
        ring }
  exact L.toContinuousLinearMap.map_tsum hF

/-- The full sum of symmetric matrices is symmetric in every pair of entries. -/
theorem isSymmetricBlockMat_tsum {d : ℕ} {ι : Type*}
    (F : ι → FullBlockMat d) (hF : Summable F)
    (hs : ∀ i, IsSymmetricBlockMat (ofFullBlockMat (F i))) :
    IsSymmetricBlockMat (ofFullBlockMat (∑' i, F i)) := by
  intro α β
  have he (α β : BlockCoord d) : (∑' i, F i) α β = ∑' i, F i α β := by
    let L : FullBlockMat d →ₗ[ℝ] ℝ :=
      { toFun := fun M => M α β
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact L.toContinuousLinearMap.map_tsum hF
  simp only [blockMatEntry_ofFullBlockMat, he]
  exact tsum_congr (fun i => by simpa only [blockMatEntry_ofFullBlockMat] using hs i α β)

/-- Every-vector quadratic evaluation commutes with a convergent full matrix
series; no replacement by scalar diagonal sums occurs. -/
theorem summable_quadratic_fullBlock {d : ℕ} {ι : Type*}
    (F : ι → FullBlockMat d) (hF : Summable F) (v : BlockVec d) :
    Summable (fun i => (1 / 2 : ℝ) * blockVecDot v
      (blockMatVecMul (ofFullBlockMat (F i)) v)) := by
  let L : FullBlockMat d →ₗ[ℝ] ℝ :=
    { toFun := fun M => (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (ofFullBlockMat M) v)
      map_add' := by
        intro M N
        simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
          Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c M
        simp only [blockVecDot_blockMatVecMul_eq_sum, blockMatEntry_ofFullBlockMat,
          Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp only [mul_assoc, mul_left_comm (toFullBlockVec v _), ← Finset.mul_sum]
        ring }
  exact hF.map L.toContinuousLinearMap L.toContinuousLinearMap.continuous

/-- The mixed response identity gives the actual full weighted block inequality.
Total volume mass one is proved before the mixed terms cancel. -/
theorem block_tsum_of_response_partition {d : ℕ} {ι : Type*} {s : Set ι} (hs : s.Countable)
    {W : Set (Vec d)} {U : ι → Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a)
    (A : BlockMat d) (Ai : ι → BlockMat d)
    (hA : ∀ p q, ResponseJ W p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul A (-p, q)) - vecDot p q)
    (hAi : ∀ i ∈ s, ∀ p q, ResponseJ (U i) p q a =
      (1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul (Ai i) (-p, q)) - vecDot p q)
    (hseries : Summable (fun i : s =>
      ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (Ai i))) :
    BlockMatLoewnerLE A (ofFullBlockMat (∑' i : s,
      ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (Ai i))) := by
  intro X
  let F : s → FullBlockMat d := fun i =>
    ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (Ai i)
  let v := vecDot (-X.1) X.2
  have hw := summable_volumeRatio (fun i hi => (hopen i hi).measurableSet) hsub hdisj
  have hwt := tsum_volumeRatio_eq_one hs hWvol (fun i hi => (hopen i hi).measurableSet)
    hsub hdisj hnull
  have hquad := summable_quadratic_fullBlock F hseries X
  have heq (i : s) : (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (ofFullBlockMat (F i)) X) =
      ((volume (U i)).toReal / (volume W).toReal) *
        ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (Ai i) X)) := by
    exact quadratic_blockScale _ (Ai i) X
  have ht : (∑' i : s, ((volume (U i)).toReal / (volume W).toReal) * ResponseJ (U i) (-X.1) X.2 a) =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (ofFullBlockMat (∑' i, F i)) X) - v := by
    calc
      _ = ∑' i : s, ((1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (ofFullBlockMat (F i)) X) -
          ((volume (U i)).toReal / (volume W).toReal) * v) := by
        apply tsum_congr
        intro i
        rw [heq i, hAi i i.2]
        simp only [neg_neg, Prod.mk.eta]
        dsimp [v]
        ring
      _ = _ := by
        rw [hquad.tsum_sub (hw.mul_right v), ← quadratic_tsum_fullBlock F hseries X,
          tsum_mul_right, hwt, one_mul]
  have hb := responseJ_le_tsum_of_partition hs hWopen hWvol hopen hsub hdisj hnull hEll (-X.1) X.2
  rw [ht, hA] at hb
  simp only [neg_neg, Prod.mk.eta] at hb
  dsimp [v] at hb
  exact (sub_le_sub_iff_right _).mp hb

/-- A finite scalar operator-norm envelope gives the Schatten membership
for symmetric full blocks, including matrix sums, differences and congruences. -/
theorem memLqSchatten_of_norm_envelope {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} (hN : 1 ≤ N) {A : CoeffSpace d → BlockMat d}
    (hAm : HasMeasurableBlock P A) (hAs : ∀ᵐ a ∂P, IsSymmetricBlockMat (A a))
    {X : CoeffSpace d → ℝ} (hX : MemLp X (ENNReal.ofReal N) P) (D : ℝ)
    (hbound : ∀ᵐ a ∂P, blockOpNorm (A a) ≤ D * X a) :
    SchattenMemLp P N A := by
  have hsm := Analysis.aestronglyMeasurable_absSchattenNorm hAm hN
  have hscalar : MemLp (fun a => absSchattenNorm N (A a)) (ENNReal.ofReal N) P := by
    apply (hX.const_mul ((2 * (d : ℝ)) ^ N⁻¹ * D)).mono' hsm
    filter_upwards [hAs, hbound] with a hs hb
    have hh := (Analysis.toFullBlockMat_isHermitian_iff (A a)).2 hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.absSchattenNorm_nonneg hh hN)]
    calc
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm (A a) :=
        Analysis.absSchattenNorm_le_dim_rpow_mul_blockOpNorm hh hN
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * (D * X a) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  refine ⟨hAm, hAs, ?_⟩
  have hi := (integrable_norm_rpow_iff hsm
    (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans_le hN)) ENNReal.ofReal_ne_top).2 hscalar
  apply hi.congr
  filter_upwards [hAs] with a hs
  simp only [Real.norm_eq_abs, abs_of_nonneg
    (Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff _).2 hs) hN),
    ENNReal.toReal_ofReal (zero_le_one.trans hN)]

/-- A common summable measurable envelope controls the actual full sum and all
finite partial sums. Symmetry and measurability are established before moments. -/
theorem full_matrix_series_envelope {d : ℕ} {ι : Type*} [Countable ι]
    (P : Measure (CoeffSpace d)) (F : ι → CoeffSpace d → FullBlockMat d)
    (hm : ∀ i, HasMeasurableBlock P (fun a => ofFullBlockMat (F i a)))
    (hs : ∀ᵐ a ∂P, ∀ i, IsSymmetricBlockMat (ofFullBlockMat (F i a)))
    (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc : Summable c)
    (X : CoeffSpace d → ℝ) (hX0 : ∀ a, 0 ≤ X a)
    (hb : ∀ᵐ a ∂P, ∀ i, ‖F i a‖ ≤ c i * X a) :
    (∀ᵐ a ∂P, Summable (fun i => F i a)) ∧
    HasMeasurableBlock P (fun a => ofFullBlockMat (∑' i, F i a)) ∧
    (∀ᵐ a ∂P, IsSymmetricBlockMat (ofFullBlockMat (∑' i, F i a))) ∧
    (∀ᵐ a ∂P, ‖∑' i, F i a‖ ≤ (∑' i, c i) * X a) ∧
    (∀ s : Finset ι, HasMeasurableBlock P (fun a => ofFullBlockMat (∑ i ∈ s, F i a)) ∧
      (∀ᵐ a ∂P, IsSymmetricBlockMat (ofFullBlockMat (∑ i ∈ s, F i a))) ∧
      (∀ᵐ a ∂P, ‖∑ i ∈ s, F i a‖ ≤ (∑' i, c i) * X a)) := by
  classical
  have hseries : ∀ᵐ a ∂P, Summable (fun i => F i a) := hb.mono fun a ha =>
    (hc.mul_right (X a)).of_norm_bounded ha
  have hfm (s : Finset ι) : HasMeasurableBlock P (fun a => ofFullBlockMat (∑ i ∈ s, F i a)) := by
    intro α β
    simp only [blockMatEntry_ofFullBlockMat, Matrix.sum_apply]
    have h := s.aestronglyMeasurable_sum (fun i _ => hm i α β)
    convert h using 1
    funext a
    simp
  have hsm : HasMeasurableBlock P (fun a => ofFullBlockMat (∑' i, F i a)) := by
    intro α β
    apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι)) (fun s => hfm s α β)
    filter_upwards [hseries] with a ha
    have h := ((continuous_apply β).tendsto _).comp
      (((continuous_apply α).tendsto _).comp ha.hasSum)
    simpa only [blockMatEntry_ofFullBlockMat] using! h
  refine ⟨hseries, hsm, ?_, ?_, ?_⟩
  · filter_upwards [hseries, hs] with a ha hs'
    exact isSymmetricBlockMat_tsum (fun i => F i a) ha hs'
  · filter_upwards [hseries, hb] with a ha hb'
    have h := ha.hasSum.norm_le_of_bounded (hc.mul_right (X a)).hasSum hb'
    simpa only [tsum_mul_right] using h
  · intro s
    refine ⟨hfm s, ?_, ?_⟩
    · filter_upwards [hs] with a hs'
      intro α β
      simp only [blockMatEntry_ofFullBlockMat, Matrix.sum_apply]
      exact Finset.sum_congr rfl (fun i _ => by
        simpa only [blockMatEntry_ofFullBlockMat] using hs' i α β)
    · filter_upwards [hb] with a hb'
      calc
        _ ≤ ∑ i ∈ s, ‖F i a‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ s, c i * X a := Finset.sum_le_sum (fun i _ => hb' i)
        _ = (∑ i ∈ s, c i) * X a := (Finset.sum_mul ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (hc.sum_le_tsum s (fun i _ => hc0 i)) (hX0 a)

/-- Dominated convergence in the actual L^N(S_N) norm for full matrix
series. The sum, every partial sum and their differences have membership before
their real norms are used. The common scalar envelope is integrable at N. -/
theorem lqSchatten_tsum_convergence {d : ℕ} {ι : Type*} [Countable ι]
    (P : Measure (CoeffSpace d)) (N : ℝ) (hN : 1 ≤ N)
    (F : ι → CoeffSpace d → FullBlockMat d)
    (hm : ∀ i, HasMeasurableBlock P (fun a => ofFullBlockMat (F i a)))
    (hs : ∀ᵐ a ∂P, ∀ i, IsSymmetricBlockMat (ofFullBlockMat (F i a)))
    (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc : Summable c)
    (X : CoeffSpace d → ℝ) (hX0 : ∀ a, 0 ≤ X a) (hX : MemLp X (ENNReal.ofReal N) P)
    (hb : ∀ᵐ a ∂P, ∀ i, ‖F i a‖ ≤ c i * X a) :
    let M := fun a => ofFullBlockMat (∑' i, F i a)
    let B := fun (s : Finset ι) a => ofFullBlockMat (∑ i ∈ s, F i a)
    SchattenMemLp P N M ∧
      (∀ s, SchattenMemLp P N (B s) ∧ SchattenMemLp P N (fun a => blockSub (B s a) (M a))) ∧
      Tendsto (fun s : Finset ι => lqSchattenNorm P N (fun a => blockSub (B s a) (M a)))
        atTop (nhds 0) := by
  classical
  intro M B
  obtain ⟨hseries, hMm, hMs, hMb, hB⟩ := full_matrix_series_envelope P F hm hs c hc0 hc X hX0 hb
  have hM : SchattenMemLp P N M := memLqSchatten_of_norm_envelope hN hMm hMs hX (∑' i, c i)
    (by simpa only [M, blockOpNorm, toFullBlockMat_ofFullBlockMat] using hMb)
  have hBmem (s : Finset ι) : SchattenMemLp P N (B s) :=
    memLqSchatten_of_norm_envelope hN (hB s).1 (hB s).2.1 hX (∑' i, c i)
      (by simpa only [B, blockOpNorm, toFullBlockMat_ofFullBlockMat] using (hB s).2.2)
  let D := fun (s : Finset ι) a => blockSub (B s a) (M a)
  have hD (s : Finset ι) : SchattenMemLp P N (D s) := (hBmem s).sub hM hN
  have hfull (s : Finset ι) (a : CoeffSpace d) :
      toFullBlockMat (D s a) = (∑ i ∈ s, F i a) - ∑' i, F i a := by
    ext α β
    cases α <;> cases β <;> rfl
  have hDs : ∀ᵐ a ∂P, ∀ s, IsSymmetricBlockMat (D s a) :=
    eventually_countable_forall.mpr (fun s => (hD s).symmetric)
  let C : ℝ := (2 * (d : ℝ)) ^ N⁻¹ * (2 * ∑' i, c i)
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hbound (s : Finset ι) : ∀ᵐ a ∂P, absSchattenNorm N (D s a) ≤ C * X a := by
    filter_upwards [hDs, hMb, (hB s).2.2] with a hs' hmb hbb
    have hh := (Analysis.toFullBlockMat_isHermitian_iff _).2 (hs' s)
    calc
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm (D s a) :=
        Analysis.absSchattenNorm_le_dim_rpow_mul_blockOpNorm hh hN
      _ = (2 * (d : ℝ)) ^ N⁻¹ * ‖(∑ i ∈ s, F i a) - ∑' i, F i a‖ := by rw [blockOpNorm, hfull]
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * (‖∑ i ∈ s, F i a‖ + ‖∑' i, F i a‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * ((∑' i, c i) * X a + (∑' i, c i) * X a) := by gcongr
      _ = _ := by dsimp [C]; ring
  have hi : Integrable (fun a => ‖C * X a‖ ^ N) P := by
    have h := (integrable_norm_rpow_iff (hX.const_mul C).aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hNp) ENNReal.ofReal_ne_top).2 (hX.const_mul C)
    simpa only [ENNReal.toReal_ofReal hN0] using h
  have hpowbound (s : Finset ι) : ∀ᵐ a ∂P, ‖absSchattenNorm N (D s a) ^ N‖ ≤ ‖C * X a‖ ^ N := by
    filter_upwards [hDs, hbound s] with a hs' hb'
    have hn := Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff _).2 (hs' s)) hN
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn N)]
    exact Real.rpow_le_rpow hn (hb'.trans (le_abs_self _)) hN0
  have hlim : ∀ᵐ a ∂P, Tendsto (fun s : Finset ι => absSchattenNorm N (D s a) ^ N) atTop (nhds 0) := by
    filter_upwards [hseries, hDs] with a hsa hds
    have ht : Tendsto (fun s : Finset ι => (∑ i ∈ s, F i a) - ∑' i, F i a) atTop (nhds 0) := by
      simpa only [sub_self] using! hsa.hasSum.sub_const (∑' i, F i a)
    have hnorm : Tendsto (fun s : Finset ι =>
        (2 * (d : ℝ)) ^ N⁻¹ * ‖(∑ i ∈ s, F i a) - ∑' i, F i a‖) atTop (nhds 0) := by
      simpa only [norm_zero, mul_zero] using ht.norm.const_mul ((2 * (d : ℝ)) ^ N⁻¹)
    have hsn : Tendsto (fun s : Finset ι => absSchattenNorm N (D s a)) atTop (nhds 0) := by
      apply squeeze_zero (fun s => Analysis.absSchattenNorm_nonneg
        ((Analysis.toFullBlockMat_isHermitian_iff _).2 (hds s)) hN) _ hnorm
      intro s
      simpa only [blockOpNorm, hfull] using Analysis.absSchattenNorm_le_dim_rpow_mul_blockOpNorm
        ((Analysis.toFullBlockMat_isHermitian_iff _).2 (hds s)) hN
    simpa only [Real.zero_rpow hNp.ne'] using!
      (Real.continuous_rpow_const hN0).continuousAt.tendsto.comp hsn
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (f := fun _ => (0 : ℝ)) (fun a => ‖C * X a‖ ^ N)
    (Eventually.of_forall fun s => (hD s).integrable.aestronglyMeasurable)
    (Eventually.of_forall hpowbound) hi hlim
  refine ⟨hM, fun s => ⟨hBmem s, hD s⟩, ?_⟩
  have hroot := (Real.continuous_rpow_const (inv_nonneg.mpr hN0)).continuousAt.tendsto.comp ht
  simpa only [lqSchattenNorm, integral_zero, Real.zero_rpow (inv_pos.mpr hNp).ne'] using! hroot

end
end HCPolySupport.HighContrast.Source
