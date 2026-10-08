/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationIndex
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio

/-!
# High-contrast homogenization: Provider.Window.BadScaleTiles

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
namespace HCPolySupport
namespace HighContrast
namespace Window
open MeasureTheory
open scoped ENNReal MatrixOrder Matrix
noncomputable section
variable {d : ℕ}
private theorem adaptedCellCenter_one (k : ℤ) (w : Fin d → ℤ) :
    adaptedCellCenter (1 : Mat d) k w = standardCellCenter k w := by
  rw [Recurrence.adaptedCellCenter_eq, matVecMul_one]
private theorem adaptedCellAt_one (k : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt (1 : Mat d) k w = standardCell d k w := by
  rw [Recurrence.adaptedCellAt_eq_image]
  have h : matVecMul (1 : Mat d) = id := by
    funext x
    exact matVecMul_one x
  rw [h, Set.image_id]

private theorem adaptedResponse_one (k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    adaptedResponse (1 : Mat d) k w a = coarseBlock (standardCell d k w) a := by
  rw [adaptedResponse, adaptedCellAt_one]

private theorem adaptedCellCenter_one_eq_intTranslation {k : ℤ} (hk : 0 ≤ k)
    (w : Fin d → ℤ) :
    adaptedCellCenter (1 : Mat d) k w =
      Source.AKL.intTranslation (fun i => (3 : ℤ) ^ k.toNat * w i) := by
  rw [adaptedCellCenter_one]
  funext i
  simp only [standardCellCenter, Source.AKL.intTranslation]
  have hp : (3 : ℝ) ^ k = (3 : ℝ) ^ k.toNat := by
    conv_lhs => rw [show k = (k.toNat : ℤ) by omega, zpow_natCast]
  rw [hp]
  push_cast
  ring

private theorem blockSize_le_of_upper_bound {H E : BlockMat d}
    (hH : IsSymmetricBlockMat H) (hHps : (toFullBlockMat H).PosSemidef)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    {c : ℝ} (hc : 0 ≤ c) (hle : BlockMatLoewnerLE H (blockScale c E)) :
    blockSize H E ≤ c := by
  refine PortableHistory.blockSize_le_of_sandwich hH hE hEpd hc ?_ ?_
  · have h := le_of_blockMatLoewnerLE hH (isSymmetricBlockMat_blockScale c hE) hle
    rwa [toFullBlockMat_blockScale] at h
  · refine Matrix.le_iff.mpr ?_
    have hrw : toFullBlockMat H - (-c) • toFullBlockMat E =
        toFullBlockMat H + c • toFullBlockMat E := by
      rw [neg_smul, sub_neg_eq_add]
    rw [hrw]
    exact hHps.add ((posDef_toFullBlockMat hE hEpd).posSemidef.smul hc)
/-- The coarse ellipticity bound holds simultaneously after every integer
translation of the sample. -/
theorem ae_coarse_bound_all_translates {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    ∀ᵐ a ∂P, ∀ v : Fin d → ℤ, ∀ m : ℤ,
      S (translateCoeff v a) ≤ (3 : ℝ) ^ m →
      ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) (translateCoeff v a))
          (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E) := by
  rw [ae_all_iff]
  intro v
  exact (Recurrence.measurePreserving_translateCoeff hstat v).quasiMeasurePreserving.ae
    hdag.coarse_bound

private theorem low_cell_bound
    {g : ℝ} {E : BlockMat d} {S : CoeffSpace d → ℝ} {h m j k : ℤ}
    (hj : j = m - h) (hh0 : 0 ≤ h) (hj0 : 0 ≤ j) (hkm : k ≤ j)
    {a : CoeffSpace d}
    (hcoarse : ∀ v : Fin d → ℤ, ∀ n : ℤ,
      S (translateCoeff v a) ≤ (3 : ℝ) ^ n →
      ∀ r : ℤ, r ≤ n → ∀ u : Fin d → ℤ,
        standardCellCenter r u ∈ centeredCube d n →
        BlockMatLoewnerLE (coarseBlock (standardCell d r u) (translateCoeff v a))
          (blockScale ((3 : ℝ) ^ (g * ((n : ℝ) - (r : ℝ)))) E))
    (hsource : ∀ y : Fin d → ℤ,
      standardCellCenter j y ∈ centeredCube d m →
      S (translateCoeff (fun i => (3 : ℤ) ^ j.toNat * y i) a) ≤ (3 : ℝ) ^ j)
    (w : Fin d → ℤ) (hw : standardCellCenter k w ∈ centeredCube d m) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale ((3 : ℝ) ^ (g * ((j : ℝ) - (k : ℝ)))) E) := by
  have hjm : j ≤ m := by omega
  have hw' : adaptedCellCenter (1 : Mat d) k w ∈ adaptedCell (1 : Mat d) m := by
    simpa only [adaptedCellCenter_one, Initialization.adaptedCell_one] using hw
  obtain ⟨y, w', hy, hw', hsplit⟩ :=
    PortableHistory.exists_index_split Matrix.PosDef.one hkm hjm hw'
  have hy' : standardCellCenter j y ∈ centeredCube d m := by
    simpa only [adaptedCellCenter_one, Initialization.adaptedCell_one] using hy
  let v : Fin d → ℤ := fun i => (3 : ℤ) ^ j.toNat * y i
  have hv : adaptedCellCenter (1 : Mat d) j y = Source.AKL.intTranslation v :=
    adaptedCellCenter_one_eq_intTranslation hj0 y
  have hcenter := PortableHistory.adaptedCellCenter_split (1 : Mat d) hkm hsplit
  have hresp := PortableHistory.adaptedResponse_split (1 : Mat d) hcenter hv a
  have hbound := hcoarse v j (hsource y hy') k hkm w'
    (by simpa only [adaptedCellCenter_one, Initialization.adaptedCell_one] using hw')
  have hresp' : coarseBlock (standardCell d k w) a =
      coarseBlock (standardCell d k w') (translateCoeff v a) := by
    simpa only [adaptedResponse_one] using hresp
  rw [hresp']
  exact hbound

private theorem high_cell_bound [NeZero d]
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    {j k m : ℤ} (hj0 : 0 ≤ j)
    (hjk : j ≤ k) (hkm : k ≤ m) {a : CoeffSpace d}
    (hlow : ∀ u : Fin d → ℤ, standardCellCenter j u ∈ centeredCube d m →
      BlockMatLoewnerLE (coarseBlock (standardCell d j u) a) E)
    (w : Fin d → ℤ) (hw : standardCellCenter k w ∈ centeredCube d m) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a) E := by
  classical
  obtain ⟨Z, hZ, hcard⟩ :=
    Recurrence.exists_finset_adaptedCellCenter_mem Matrix.PosDef.one hjk
  have hZne : Z.Nonempty := by rw [← Finset.card_pos, hcard]; positivity
  have hk0 : 0 ≤ k := hj0.trans hjk
  let v : Fin d → ℤ := fun i => (3 : ℤ) ^ k.toNat * w i
  have hv : adaptedCellCenter (1 : Mat d) k w = Source.AKL.intTranslation v :=
    adaptedCellCenter_one_eq_intTranslation hk0 w
  have hparentCenter : adaptedCellCenter (1 : Mat d) k w =
      adaptedCellCenter (1 : Mat d) k w + adaptedCellCenter (1 : Mat d) k 0 := by
    rw [adaptedCellCenter_one, adaptedCellCenter_one]
    have hz : standardCellCenter k (0 : Fin d → ℤ) = 0 := by
      funext i; simp [standardCellCenter]
    rw [hz, add_zero]
  have hparentResp : adaptedResponse (1 : Mat d) k w a =
      adaptedResponse (1 : Mat d) k 0 (translateCoeff v a) :=
    PortableHistory.adaptedResponse_split (1 : Mat d) hparentCenter hv a
  have hparent : toFullBlockMat (coarseBlock (adaptedCell (1 : Mat d) k)
      (translateCoeff v a)) ≤
      (Z.card : ℝ)⁻¹ • ∑ u ∈ Z,
        toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j u)
          (translateCoeff v a)) := by
    exact Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average
      Matrix.PosDef.one hjk hZ (translateCoeff v a)
  have hchild : ∀ u ∈ Z,
      toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j u)
        (translateCoeff v a)) ≤ toFullBlockMat E := by
    intro u hu
    have hu' : adaptedCellCenter (1 : Mat d) j u ∈ adaptedCell (1 : Mat d) k := by
      have : u ∈ (↑Z : Set (Fin d → ℤ)) := Finset.mem_coe.mpr hu
      rwa [hZ] at this
    let W : Fin d → ℤ := fun i => u i + (3 : ℤ) ^ (k - j).toNat * w i
    have hsplit : ∀ i, W i = u i + (3 : ℤ) ^ (k - j).toNat * w i := fun _ => rfl
    have hcenter := PortableHistory.adaptedCellCenter_split (1 : Mat d) hjk hsplit
    have hmemParent : adaptedCellCenter (1 : Mat d) j W ∈
        adaptedCellAt (1 : Mat d) k w := by
      refine ⟨adaptedCellCenter (1 : Mat d) j u, hu', ?_⟩
      exact hcenter.symm
    have hparentSub := Recurrence.adaptedCellAt_subset_adaptedCell
      Matrix.PosDef.one hkm
      (by simpa only [adaptedCellCenter_one, Initialization.adaptedCell_one] using hw)
    have hWm : standardCellCenter j W ∈ centeredCube d m := by
      simpa only [adaptedCellCenter_one, Initialization.adaptedCell_one] using hparentSub hmemParent
    have hglobal := hlow W hWm
    have hresp := PortableHistory.adaptedResponse_split (1 : Mat d) hcenter hv a
    have hglobalFull := le_of_blockMatLoewnerLE
      (isSymmetricBlockMat_coarseBlock _ a) hE hglobal
    have hrespFull :
        toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j W) a) =
          toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j u)
            (translateCoeff v a)) := by
      simpa only [adaptedResponse] using congrArg toFullBlockMat hresp
    rw [← hrespFull, adaptedCellAt_one]
    exact hglobalFull
  have havg : (Z.card : ℝ)⁻¹ • ∑ u ∈ Z,
      toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j u)
        (translateCoeff v a)) ≤ toFullBlockMat E := by
    have hsum : ∑ u ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) j u)
        (translateCoeff v a)) ≤ ∑ _u ∈ Z, toFullBlockMat E :=
      Finset.sum_le_sum fun u hu => hchild u hu
    have hs := smul_le_smul_of_nonneg_left hsum
      (inv_nonneg.mpr (Nat.cast_nonneg Z.card) : 0 ≤ (Z.card : ℝ)⁻¹)
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hZne.card_pos.ne'), one_smul] at hs
    exact hs
  have hfull := hparent.trans havg
  rw [Initialization.adaptedCell_one] at hfull
  have hrespFull := congrArg toFullBlockMat hparentResp
  simp only [adaptedResponse, adaptedCellAt_one, standardCell_zero] at hrespFull
  apply blockMatLoewnerLE_of_le
  rw [hrespFull]
  exact hfull

private theorem cell_bound_of_tile_sources [NeZero d]
    {g : ℝ} {E : BlockMat d} {S : CoeffSpace d → ℝ} {h m k : ℤ}
    (hE : IsSymmetricBlockMat E) (hh0 : 0 ≤ h) (hhm : h ≤ m) {a : CoeffSpace d}
    (hcoarse : ∀ v : Fin d → ℤ, ∀ n : ℤ,
      S (translateCoeff v a) ≤ (3 : ℝ) ^ n →
      ∀ r : ℤ, r ≤ n → ∀ u : Fin d → ℤ,
        standardCellCenter r u ∈ centeredCube d n →
        BlockMatLoewnerLE (coarseBlock (standardCell d r u) (translateCoeff v a))
          (blockScale ((3 : ℝ) ^ (g * ((n : ℝ) - (r : ℝ)))) E))
    (hsource : ∀ y : Fin d → ℤ,
      standardCellCenter (m - h) y ∈ centeredCube d m →
      S (translateCoeff (fun i => (3 : ℤ) ^ (m - h).toNat * y i) a) ≤
        (3 : ℝ) ^ (m - h))
    (hkm : k ≤ m) (w : Fin d → ℤ)
    (hw : standardCellCenter k w ∈ centeredCube d m) :
    BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale ((3 : ℝ) ^
        (g * max ((m : ℝ) - (h : ℝ) - (k : ℝ)) 0)) E) := by
  have hj0 : 0 ≤ m - h := by omega
  by_cases hlow : k ≤ m - h
  · have hb := low_cell_bound rfl hh0 hj0 hlow hcoarse hsource w hw
    have hnonneg : 0 ≤ (m : ℝ) - (h : ℝ) - (k : ℝ) := by
      exact_mod_cast (sub_nonneg.mpr hlow)
    rw [max_eq_left hnonneg]
    simpa only [Int.cast_sub] using hb
  · have hhigh : m - h ≤ k := (lt_of_not_ge hlow).le
    have hchild : ∀ u : Fin d → ℤ,
        standardCellCenter (m - h) u ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d (m - h) u) a) E := by
      intro u hu
      have hb := low_cell_bound rfl hh0 hj0 le_rfl hcoarse hsource u hu
      simpa only [sub_self, Int.cast_sub, sub_self, mul_zero, Real.rpow_zero,
        blockScale_one] using hb
    have hb := high_cell_bound hE hj0 hhigh hkm hchild w hw
    have hneg : (m : ℝ) - (h : ℝ) - (k : ℝ) ≤ 0 := by
      exact_mod_cast sub_nonpos.mpr hhigh
    simpa only [max_eq_right hneg, mul_zero, Real.rpow_zero, blockScale_one] using hb

private theorem not_badScaleEvent_of_tile_sources [NeZero d]
    {g : ℝ} {E : BlockMat d} {S : CoeffSpace d → ℝ} {h m : ℤ}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hh0 : 0 ≤ h) (hhm : h ≤ m) {a : CoeffSpace d}
    (hcoarse : ∀ v : Fin d → ℤ, ∀ n : ℤ,
      S (translateCoeff v a) ≤ (3 : ℝ) ^ n →
      ∀ r : ℤ, r ≤ n → ∀ u : Fin d → ℤ,
        standardCellCenter r u ∈ centeredCube d n →
        BlockMatLoewnerLE (coarseBlock (standardCell d r u) (translateCoeff v a))
          (blockScale ((3 : ℝ) ^ (g * ((n : ℝ) - (r : ℝ)))) E))
    (hsource : ∀ y : Fin d → ℤ,
      standardCellCenter (m - h) y ∈ centeredCube d m →
      S (translateCoeff (fun i => (3 : ℤ) ^ (m - h).toNat * y i) a) ≤
        (3 : ℝ) ^ (m - h)) :
    ¬badScaleEvent g E h m a := by
  rw [badScaleEvent]
  apply not_lt_of_ge
  refine iSup_le fun k => iSup_le fun hkm => iSup_le fun w => iSup_le fun hw => ?_
  have hcell := cell_bound_of_tile_sources hE hh0 hhm hcoarse hsource hkm w hw
  have hAsym := isSymmetricBlockMat_coarseBlock (standardCell d k w) a
  have hApsd := (posDef_toFullBlockMat hAsym
    (Recurrence.blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet (translateCube w (originCube d k)))
      (Recurrence.standardCell_nonempty k w) a)).posSemidef
  let x : ℝ := g * max ((m : ℝ) - (h : ℝ) - (k : ℝ)) 0
  have hsize : blockSize (coarseBlock (standardCell d k w) a) E ≤ (3 : ℝ) ^ x :=
    blockSize_le_of_upper_bound hAsym hApsd hE hEpd (by positivity) hcell
  apply ENNReal.ofReal_le_one.mpr
  have hnegx : -g * max ((m : ℝ) - (h : ℝ) - (k : ℝ)) 0 = -x := by
    dsimp only [x]
    ring
  rw [hnegx]
  calc
    (3 : ℝ) ^ (-x) * blockSize (coarseBlock (standardCell d k w) a) E
        ≤ (3 : ℝ) ^ (-x) * (3 : ℝ) ^ x :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = 1 := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]; simp

private theorem badScaleEvent_imp_exists_source_tail [NeZero d]
    {g : ℝ} {E : BlockMat d} {S : CoeffSpace d → ℝ} {h m : ℤ}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hh0 : 0 ≤ h) (hhm : h ≤ m) {a : CoeffSpace d}
    (hcoarse : ∀ v : Fin d → ℤ, ∀ n : ℤ,
      S (translateCoeff v a) ≤ (3 : ℝ) ^ n →
      ∀ r : ℤ, r ≤ n → ∀ u : Fin d → ℤ,
        standardCellCenter r u ∈ centeredCube d n →
        BlockMatLoewnerLE (coarseBlock (standardCell d r u) (translateCoeff v a))
          (blockScale ((3 : ℝ) ^ (g * ((n : ℝ) - (r : ℝ)))) E))
    (hbad : badScaleEvent g E h m a) :
    ∃ y : Fin d → ℤ, standardCellCenter (m - h) y ∈ centeredCube d m ∧
      (3 : ℝ) ^ (m - h) <
        S (translateCoeff (fun i => (3 : ℤ) ^ (m - h).toNat * y i) a) := by
  by_contra hn
  push Not at hn
  apply not_badScaleEvent_of_tile_sources hE hEpd hh0 hhm hcoarse
    (fun y hy => hn y hy) hbad

/-- A bad window scale is bounded by the union of the translated source tails
over the aligned tiles of the window. -/
theorem measureReal_badScaleEvent_le_tiles [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {h m : ℤ} (hh0 : 0 ≤ h) (hhm : h ≤ m) :
    P.real {a : CoeffSpace d | badScaleEvent g E h m a} ≤
      (3 : ℝ) ^ (d * h.toNat) * (Ψ ((3 : ℝ) ^ (m - h)))⁻¹ := by
  classical
  have hjm : m - h ≤ m := by omega
  obtain ⟨Z, hZ, hcard⟩ :=
    Recurrence.exists_finset_adaptedCellCenter_mem (q := (1 : Mat d)) Matrix.PosDef.one hjm
  let T : (Fin d → ℤ) → Set (CoeffSpace d) := fun y =>
    {a | (3 : ℝ) ^ (m - h) <
      S (translateCoeff (fun i => (3 : ℤ) ^ (m - h).toNat * y i) a)}
  have hsub : ∀ᵐ a ∂P, a ∈ {a : CoeffSpace d | badScaleEvent g E h m a} →
      a ∈ ⋃ y ∈ Z, T y := by
    filter_upwards [ae_coarse_bound_all_translates hstat hdag] with a ha hbad
    obtain ⟨y, hy, htail⟩ := badScaleEvent_imp_exists_source_tail
      hdag.refBlock_isSymm hdag.refBlock_posDef hh0 hhm ha hbad
    have hyZ : y ∈ Z := by
      have : y ∈ (↑Z : Set (Fin d → ℤ)) := by
        rw [hZ]
        simpa only [adaptedCellCenter_one, Initialization.adaptedCell_one] using! hy
      exact Finset.mem_coe.mp this
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyZ, htail⟩⟩
  have hmono : P.real {a : CoeffSpace d | badScaleEvent g E h m a} ≤
      P.real (⋃ y ∈ Z, T y) := by
    exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have htail : ∀ y : Fin d → ℤ, P.real (T y) ≤ (Ψ ((3 : ℝ) ^ (m - h)))⁻¹ := by
    intro y
    let v : Fin d → ℤ := fun i => (3 : ℤ) ^ (m - h).toNat * y i
    have hset : T y = (translateCoeff v) ⁻¹'
        IndependentSums.upperTailEvent S ((3 : ℝ) ^ (m - h)) := rfl
    have hmeas : MeasurableSet
        (IndependentSums.upperTailEvent S ((3 : ℝ) ^ (m - h))) :=
      measurableSet_lt measurable_const hdag.source_measurable
    have hmeasure := (Recurrence.measurePreserving_translateCoeff hstat v).measure_preimage
      hmeas.nullMeasurableSet
    have hmeasureReal :
        P.real ((translateCoeff v) ⁻¹'
          IndependentSums.upperTailEvent S ((3 : ℝ) ^ (m - h))) =
        P.real (IndependentSums.upperTailEvent S ((3 : ℝ) ^ (m - h))) :=
      congrArg ENNReal.toReal hmeasure
    rw [hset, hmeasureReal]
    exact hdag.source_tail _ (by positivity)
  calc
    P.real {a : CoeffSpace d | badScaleEvent g E h m a}
        ≤ P.real (⋃ y ∈ Z, T y) := hmono
    _ ≤ ∑ y ∈ Z, P.real (T y) := measureReal_biUnion_finset_le Z T
    _ ≤ ∑ _y ∈ Z, (Ψ ((3 : ℝ) ^ (m - h)))⁻¹ :=
      Finset.sum_le_sum fun y _ => htail y
    _ = (3 : ℝ) ^ (d * h.toNat) * (Ψ ((3 : ℝ) ^ (m - h)))⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      norm_num

end
end Window
end HighContrast
end HCPolySupport
