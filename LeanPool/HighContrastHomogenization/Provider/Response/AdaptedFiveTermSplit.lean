/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakOptimizerStationarity
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates

/-!
# High-contrast homogenization: Provider.Response.AdaptedFiveTermSplit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-! # Cutoff-mean splitting on adapted cells
An aligned cutoff-defect mean splits into parent--child defect and within-cell oscillation;
stationarity cancels the remaining child-optimizer mean. -/
namespace HCPolySupport.HighContrast.Response
open Book.Ch02 MeasureTheory
noncomputable section
variable {d : ℕ}
private theorem toFullBlockVec_blockCellAverage (U : Set (Vec d))
    (F : Vec d → BlockVec d) (alpha : BlockCoord d) : toFullBlockVec
      (blockCellAverage U F) alpha = volumeAverage U (fun x ↦ toFullBlockVec (F x) alpha) := by
  cases alpha <;> rfl
private theorem integral_avsum_eq_avsum_integral {P : Measure (CoeffSpace d)}
    {iota : Type*} (Z : Finset iota) (F : iota → CoeffSpace d → ℝ)
    (hF : ∀ z ∈ Z, Integrable (F z) P) :
    (∫ a, avsum Z (fun z ↦ F z a) ∂P) = avsum Z (fun z ↦ ∫ a, F z a ∂P) := by
  unfold avsum
  rw [integral_const_mul, integral_finsetSum Z hF]
private theorem sum_mul_avsum {iota : Type*} (Z : Finset iota) (c : Vec d)
    (F : Fin d → iota → ℝ) : ∑ i, c i * avsum Z (F i) =
      avsum Z (fun z ↦ ∑ i, c i * F i z) := by
  unfold avsum
  calc
    ∑ i, c i * (((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, F i z) =
        ((Z.card : ℝ))⁻¹ * ∑ i, c i * ∑ z ∈ Z, F i z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ((Z.card : ℝ))⁻¹ * ∑ i, ∑ z ∈ Z, c i * F i z := by
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ Finset.mul_sum _ _ _
    _ = ((Z.card : ℝ))⁻¹ * ∑ z ∈ Z, ∑ i, c i * F i z := by
      rw [Finset.sum_comm]
private theorem integrableOn_diagonalWeakState_readout {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (p r : Vec d)
    (alpha : BlockCoord d) : IntegrableOn (fun x ↦ toFullBlockVec
      (diagonalWeakState hq t a p r x) alpha) (adaptedCell q t) volume := by
  obtain ⟨hgrad, hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  cases alpha with
  | inl i => simpa only [toFullBlockVec, adaptedDomain_carrier] using
      integrableOn_component (U := adaptedDomain hq t) hgrad i
  | inr i => simpa only [toFullBlockVec, adaptedDomain_carrier] using
      integrableOn_component (U := adaptedDomain hq t) hflux i
private theorem integrableOn_cutoff_mul_diagonalWeakState_readout [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (a : CoeffSpace d) (p r : Vec d)
    (alpha : BlockCoord d) : IntegrableOn (fun x ↦ adaptedPreYoungCutoff q hq t x *
      toFullBlockVec (diagonalWeakState hq t a p r x) alpha) (adaptedCell q t) volume := by
  have hbase := integrableOn_diagonalWeakState_readout hq t a p r alpha
  have hmeas : AEStronglyMeasurable (adaptedPreYoungCutoff q hq t)
      (volumeMeasureOn (adaptedCell q t)) :=
    (adaptedPreYoungCutoff_smooth hq t).continuous.aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂volumeMeasureOn (adaptedCell q t),
      ‖adaptedPreYoungCutoff q hq t x‖ ≤ 2 :=
    _root_.Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact adaptedPreYoungCutoff_le_two hq t x
      · exact adaptedPreYoungCutoff_nonneg hq t x
  simpa only [mul_comm] using! hbase.bdd_mul hmeas hbdd
private theorem annealed_cutoff_readout_split
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    {s t : ℤ} (hst : s ≤ t) (X : CoeffSpace d → Vec d → BlockVec d)
    (Y : (Fin d → ℤ) → CoeffSpace d → Vec d → BlockVec d)
    (alpha : BlockCoord d)
    (hspace : ∀ a, IntegrableOn (fun x ↦ toFullBlockVec (X a x) alpha)
      (adaptedCell q t) volume)
    (hcutSpace : ∀ a, IntegrableOn (fun x ↦ adaptedPreYoungCutoff q hq t x *
      toFullBlockVec (X a x) alpha) (adaptedCell q t) volume)
    (hparent : ∀ w ∈ alignedIndex q s t, Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w) (X a)) alpha) P)
    (hosc : ∀ w ∈ alignedIndex q s t, Integrable (fun a ↦ volumeAverage
      (adaptedCellAt q s w) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (X a x) alpha)) P)
    (hzero : avsum (alignedIndex q s t) (fun w ↦
      (1 - volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
        ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a)) alpha ∂P) = 0) :
    (∫ a, volumeAverage (adaptedCell q t) (fun x ↦
        (adaptedPreYoungCutoff q hq t x - 1) * toFullBlockVec (X a x) alpha) ∂P) =
      avsum (alignedIndex q s t) (fun w ↦
        (1 - volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
          ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a)) alpha ∂P) -
            ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (X a)) alpha ∂P)) +
        avsum (alignedIndex q s t) (fun w ↦ ∫ a, volumeAverage
          (adaptedCellAt q s w) (fun x ↦
            (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
              (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (X a x) alpha) ∂P) := by
  let Z := alignedIndex q s t
  let weight : (Fin d → ℤ) → ℝ := fun w ↦
    1 - volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)
  let parent : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a ↦
    toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (X a)) alpha
  let child : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a ↦
    toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a)) alpha
  let oscillation : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a ↦
    volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - volumeAverage (adaptedCellAt q s w)
        (adaptedPreYoungCutoff q hq t)) * toFullBlockVec (X a x) alpha)
  have hcell : ∀ a w, w ∈ Z → volumeAverage (adaptedCellAt q s w) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - 1) * toFullBlockVec (X a x) alpha) =
      -weight w * parent w a + oscillation w a := by
    intro a w hw
    have hsub := adaptedCellAt_subset_of_mem_alignedIndex hq hst
      (show w ∈ alignedIndex q s t by simpa only [Z] using hw)
    have hF := (hspace a).mono_set hsub
    have hcutF := (hcutSpace a).mono_set hsub
    dsimp only [weight, parent, oscillation]
    rw [toFullBlockVec_blockCellAverage]
    rw [show (fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
        toFullBlockVec (X a x) alpha) = (fun x ↦ adaptedPreYoungCutoff q hq t x *
          toFullBlockVec (X a x) alpha) - fun x ↦ toFullBlockVec (X a x) alpha by
          funext x; dsimp; ring, volumeAverage_sub hcutF hF]
    have hoscEq : (fun x ↦ (adaptedPreYoungCutoff q hq t x - volumeAverage
        (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
          toFullBlockVec (X a x) alpha) =
        (fun x ↦ adaptedPreYoungCutoff q hq t x * toFullBlockVec (X a x) alpha) -
          (volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) •
            (fun x ↦ toFullBlockVec (X a x) alpha) := by funext x; simp; ring
    have hsmul : IntegrableOn ((volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq
      t)) •
        fun x ↦ toFullBlockVec (X a x) alpha) (adaptedCellAt q s w) volume := by
      simpa only [Pi.smul_apply, smul_eq_mul] using! hF.const_mul _
    rw [hoscEq, volumeAverage_sub hcutF hsmul, volumeAverage_smul]
    ring
  have hpoint : (fun a ↦ volumeAverage (adaptedCell q t) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - 1) * toFullBlockVec (X a x) alpha)) =
      fun a ↦ avsum Z (fun w ↦ -weight w * parent w a + oscillation w a) := by
    funext a
    have hint : IntegrableOn (fun x ↦ (adaptedPreYoungCutoff q hq t x - 1) *
        toFullBlockVec (X a x) alpha) (adaptedCell q t) volume := by
      refine (hcutSpace a).sub (hspace a) |>.congr ?_
      filter_upwards with x
      dsimp
      ring
    rw [← avsum_volumeAverage_adaptedCellAt_eq hq hst hint]
    rw [avsum_eq, avsum_eq]
    congr 1
    exact Finset.sum_congr rfl fun w hw ↦ hcell a w hw
  rw [hpoint, integral_avsum_eq_avsum_integral Z]
  · have hrewrite : avsum Z (fun w ↦ ∫ a, -weight w * parent w a + oscillation w a ∂P) =
        avsum Z (fun w ↦ -weight w * (∫ a, parent w a ∂P)) +
          avsum Z (fun w ↦ ∫ a, oscillation w a ∂P) := by
      unfold avsum
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun w hw ↦ by
        change (∫ a, -weight w * parent w a + oscillation w a ∂P) = _
        rw [integral_add ((hparent w (by simpa only [Z] using hw)).const_mul _)
          (hosc w (by simpa only [Z] using hw)), integral_const_mul]
    rw [hrewrite]
    have hdefect : avsum Z (fun w ↦ weight w *
        ((∫ a, child w a ∂P) - ∫ a, parent w a ∂P)) =
        avsum Z (fun w ↦ -weight w * (∫ a, parent w a ∂P)) := by
      calc
        _ = avsum Z (fun w ↦ weight w * (∫ a, child w a ∂P)) +
            avsum Z (fun w ↦ -weight w * (∫ a, parent w a ∂P)) := by
          rw [← avsum_add]
          apply congrArg (avsum Z); funext w; ring
        _ = _ := by rw [show avsum Z (fun w ↦ weight w *
            (∫ a, child w a ∂P)) = 0 by simpa only [Z, weight, child] using hzero,
          zero_add]
    simp only [Z, weight, parent, child, oscillation, hdefect]
  · intro w hw
    exact ((hparent w (by simpa only [Z] using hw)).const_mul _).add
      (hosc w (by simpa only [Z] using hw))
private theorem vecDot_annealed_cutoff_split
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef) {s t : ℤ}
    (hst : s ≤ t) (X : CoeffSpace d → Vec d → BlockVec d)
    (Y : (Fin d → ℤ) → CoeffSpace d → Vec d → BlockVec d)
    (coord : Fin d → BlockCoord d) (c : Vec d)
    (hspace : ∀ a i, IntegrableOn (fun x ↦ toFullBlockVec (X a x) (coord i))
      (adaptedCell q t) volume)
    (hcutSpace : ∀ a i, IntegrableOn (fun x ↦ adaptedPreYoungCutoff q hq t x *
      toFullBlockVec (X a x) (coord i)) (adaptedCell q t) volume)
    (hparent : ∀ w ∈ alignedIndex q s t, ∀ i, Integrable (fun a ↦ toFullBlockVec
      (blockCellAverage (adaptedCellAt q s w) (X a)) (coord i)) P)
    (hosc : ∀ w ∈ alignedIndex q s t, ∀ i, Integrable (fun a ↦ volumeAverage
      (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
          toFullBlockVec (X a x) (coord i))) P)
    (hzero : ∀ i, avsum (alignedIndex q s t) (fun w ↦
      (1 - volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
        ∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a)) (coord i) ∂P) = 0) :
    vecDot c (fun i ↦ ∫ a, volumeAverage (adaptedCell q t) (fun x ↦
      (adaptedPreYoungCutoff q hq t x - 1) * toFullBlockVec (X a x) (coord i)) ∂P) =
      avsum (alignedIndex q s t) (fun w ↦
        (1 - volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
          ∑ i, c i * ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w)
            (Y w a)) (coord i) ∂P) - ∫ a, toFullBlockVec
              (blockCellAverage (adaptedCellAt q s w) (X a)) (coord i) ∂P)) +
        avsum (alignedIndex q s t) (fun w ↦ ∑ i, c i * ∫ a, volumeAverage
          (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
            volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
              toFullBlockVec (X a x) (coord i)) ∂P) := by
  simp only [vecDot]
  have hi := fun i ↦ annealed_cutoff_readout_split hq hst X Y (coord i)
    (fun a ↦ hspace a i) (fun a ↦ hcutSpace a i)
    (fun w hw ↦ hparent w hw i) (fun w hw ↦ hosc w hw i) (hzero i)
  simp_rw [hi, mul_add]
  rw [Finset.sum_add_distrib, sum_mul_avsum, sum_mul_avsum]
  apply congrArg₂ (·+·)
  · apply congrArg (avsum (alignedIndex q s t)); funext w
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  · rfl
/-- The primal gradient cutoff mean splits into its defect and oscillation halves. -/ theorem
  vecDot_profilePrimalCutoffMean_fst_eq_defect_add_oscillation [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hint : HasFiniteAdaptedMean P q s) (g : Mat d) (hg : IsSkewMat g)
    (p r Qcen : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid;
    let X := fun a ↦ diagonalWeakState hq t (a.subSkew g hg) p r;
    let Y := fun w a ↦ diagonalWeakChildState hq s w (a.subSkew g hg) p r;
    ((∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ toFullBlockVec
        (blockCellAverage (adaptedCellAt q s w) (X a)) alpha) P) ∧
      (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ volumeAverage
        (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x - volumeAverage
          (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec (X a x) alpha)) P)) →
      vecDot Qcen (profilePrimalCutoffMean P hq t (fun a ↦ a.subSkew g hg)
        (adaptedPreYoungCutoff q hq t) p r).1 =
        avsum (alignedIndex q s t) (fun w ↦ (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) * ∑ i, Qcen i *
            ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inl i) ∂P) - ∫ a, toFullBlockVec (blockCellAverage
                (adaptedCellAt q s w) (X a)) (Sum.inl i) ∂P)) +
          avsum (alignedIndex q s t) (fun w ↦ ∑ i, Qcen i * ∫ a, volumeAverage
            (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
              volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
                toFullBlockVec (X a x) (Sum.inl i)) ∂P) := by
  dsimp only
  intro hInt
  simpa only [profilePrimalCutoffMean, volumeAverageVec, toFullBlockVec, Pi.smul_apply,
    smul_eq_mul] using
    vecDot_annealed_cutoff_split (P := P) (Recurrence.posDef_of_isRoundedGrid hgrid) hst
      (fun a ↦ diagonalWeakState _ t (a.subSkew g hg) p r)
      (fun w a ↦ diagonalWeakChildState _ s w (a.subSkew g hg) p r)
      Sum.inl Qcen (fun a i ↦ integrableOn_diagonalWeakState_readout _ t
        (a.subSkew g hg) p r (Sum.inl i))
      (fun a i ↦ integrableOn_cutoff_mul_diagonalWeakState_readout _ t
        (a.subSkew g hg) p r (Sum.inl i))
      (fun w hw i ↦ hInt.1 w hw (Sum.inl i)) (fun w hw i ↦ hInt.2 w hw (Sum.inl i))
      (fun i ↦ avsum_one_sub_cutoffAverage_mul_integral_childState_subSkew_eq_zero
        hstat hgrid hls hst hint g hg p r (Sum.inl i))
/-- The primal flux cutoff mean splits into its defect and oscillation halves. -/ theorem
  vecDot_profilePrimalCutoffMean_snd_eq_defect_add_oscillation [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hint : HasFiniteAdaptedMean P q s) (g : Mat d) (hg : IsSkewMat g)
    (p r Pcen : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid;
    let X := fun a ↦ diagonalWeakState hq t (a.subSkew g hg) p r;
    let Y := fun w a ↦ diagonalWeakChildState hq s w (a.subSkew g hg) p r;
    ((∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ toFullBlockVec
        (blockCellAverage (adaptedCellAt q s w) (X a)) alpha) P) ∧
      (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ volumeAverage
        (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x - volumeAverage
          (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec (X a x) alpha)) P)) →
      vecDot Pcen (profilePrimalCutoffMean P hq t (fun a ↦ a.subSkew g hg)
        (adaptedPreYoungCutoff q hq t) p r).2 =
        avsum (alignedIndex q s t) (fun w ↦ (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) * ∑ i, Pcen i *
            ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inr i) ∂P) - ∫ a, toFullBlockVec (blockCellAverage
                (adaptedCellAt q s w) (X a)) (Sum.inr i) ∂P)) +
          avsum (alignedIndex q s t) (fun w ↦ ∑ i, Pcen i * ∫ a, volumeAverage
            (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
              volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
                toFullBlockVec (X a x) (Sum.inr i)) ∂P) := by
  dsimp only
  intro hInt
  simpa only [profilePrimalCutoffMean, volumeAverageVec, toFullBlockVec, Pi.smul_apply,
    smul_eq_mul] using
    vecDot_annealed_cutoff_split (P := P) (Recurrence.posDef_of_isRoundedGrid hgrid) hst
      (fun a ↦ diagonalWeakState _ t (a.subSkew g hg) p r)
      (fun w a ↦ diagonalWeakChildState _ s w (a.subSkew g hg) p r)
      Sum.inr Pcen (fun a i ↦ integrableOn_diagonalWeakState_readout _ t
        (a.subSkew g hg) p r (Sum.inr i))
      (fun a i ↦ integrableOn_cutoff_mul_diagonalWeakState_readout _ t
        (a.subSkew g hg) p r (Sum.inr i))
      (fun w hw i ↦ hInt.1 w hw (Sum.inr i)) (fun w hw i ↦ hInt.2 w hw (Sum.inr i))
      (fun i ↦ avsum_one_sub_cutoffAverage_mul_integral_childState_subSkew_eq_zero
        hstat hgrid hls hst hint g hg p r (Sum.inr i))
/-- The adjoint gradient cutoff mean has the independently canceled split. -/ theorem
  vecDot_profileAdjointCutoffMean_fst_eq_defect_add_oscillation [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hint : HasFiniteAdaptedMean P q s) (g : Mat d) (hg : IsSkewMat g)
    (p r Qcen : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid;
    let X := fun a ↦ diagonalWeakState hq t (a.subSkew g hg).transpose p r;
    let Y := fun w a ↦ diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r;
    ((∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ toFullBlockVec
        (blockCellAverage (adaptedCellAt q s w) (X a)) alpha) P) ∧
      (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ volumeAverage
        (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x - volumeAverage
          (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec (X a x) alpha)) P)) →
      vecDot Qcen (profileAdjointCutoffMean P hq t (fun a ↦ a.subSkew g hg)
        (adaptedPreYoungCutoff q hq t) p r).1 =
        avsum (alignedIndex q s t) (fun w ↦ (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) * ∑ i, Qcen i *
            ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inl i) ∂P) - ∫ a, toFullBlockVec (blockCellAverage
                (adaptedCellAt q s w) (X a)) (Sum.inl i) ∂P)) +
          avsum (alignedIndex q s t) (fun w ↦ ∑ i, Qcen i * ∫ a, volumeAverage
            (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
              volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
                toFullBlockVec (X a x) (Sum.inl i)) ∂P) := by
  dsimp only
  intro hInt
  simpa only [profileAdjointCutoffMean, diagonalWeakAdjointState_eq, toFullBlockVec,
    Pi.smul_apply, smul_eq_mul] using! vecDot_annealed_cutoff_split (P := P)
      (Recurrence.posDef_of_isRoundedGrid hgrid) hst
      (fun a ↦ diagonalWeakState _ t (a.subSkew g hg).transpose p r)
      (fun w a ↦ diagonalWeakChildState _ s w (a.subSkew g hg).transpose p r)
      Sum.inl Qcen (fun a i ↦ integrableOn_diagonalWeakState_readout _ t
        (a.subSkew g hg).transpose p r (Sum.inl i))
      (fun a i ↦ integrableOn_cutoff_mul_diagonalWeakState_readout _ t
        (a.subSkew g hg).transpose p r (Sum.inl i))
      (fun w hw i ↦ hInt.1 w hw (Sum.inl i)) (fun w hw i ↦ hInt.2 w hw (Sum.inl i))
      (fun i ↦ avsum_one_sub_cutoffAverage_mul_integral_childState_adjointSubSkew_eq_zero
        hstat hgrid hls hst hint g hg p r (Sum.inl i))
/-- The adjoint flux cutoff mean has the independently canceled split. -/ theorem
  vecDot_profileAdjointCutoffMean_snd_eq_defect_add_oscillation [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {l s t : ℤ} {q : Mat d}
    (hgrid : IsRoundedGrid l q) (hls : l ≤ s) (hst : s ≤ t)
    (hint : HasFiniteAdaptedMean P q s) (g : Mat d) (hg : IsSkewMat g)
    (p r Pcen : Vec d) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid;
    let X := fun a ↦ diagonalWeakState hq t (a.subSkew g hg).transpose p r;
    let Y := fun w a ↦ diagonalWeakChildState hq s w (a.subSkew g hg).transpose p r;
    ((∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ toFullBlockVec
        (blockCellAverage (adaptedCellAt q s w) (X a)) alpha) P) ∧
      (∀ w ∈ alignedIndex q s t, ∀ alpha, Integrable (fun a ↦ volumeAverage
        (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x - volumeAverage
          (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec (X a x) alpha)) P)) →
      vecDot Pcen (profileAdjointCutoffMean P hq t (fun a ↦ a.subSkew g hg)
        (adaptedPreYoungCutoff q hq t) p r).2 =
        avsum (alignedIndex q s t) (fun w ↦ (1 - volumeAverage (adaptedCellAt q s w)
          (adaptedPreYoungCutoff q hq t)) * ∑ i, Pcen i *
            ((∫ a, toFullBlockVec (blockCellAverage (adaptedCellAt q s w) (Y w a))
              (Sum.inr i) ∂P) - ∫ a, toFullBlockVec (blockCellAverage
                (adaptedCellAt q s w) (X a)) (Sum.inr i) ∂P)) +
          avsum (alignedIndex q s t) (fun w ↦ ∑ i, Pcen i * ∫ a, volumeAverage
            (adaptedCellAt q s w) (fun x ↦ (adaptedPreYoungCutoff q hq t x -
              volumeAverage (adaptedCellAt q s w) (adaptedPreYoungCutoff q hq t)) *
                toFullBlockVec (X a x) (Sum.inr i)) ∂P) := by
  dsimp only
  intro hInt
  simpa only [profileAdjointCutoffMean, diagonalWeakAdjointState_eq, toFullBlockVec,
    Pi.smul_apply, smul_eq_mul] using! vecDot_annealed_cutoff_split (P := P)
      (Recurrence.posDef_of_isRoundedGrid hgrid) hst
      (fun a ↦ diagonalWeakState _ t (a.subSkew g hg).transpose p r)
      (fun w a ↦ diagonalWeakChildState _ s w (a.subSkew g hg).transpose p r)
      Sum.inr Pcen (fun a i ↦ integrableOn_diagonalWeakState_readout _ t
        (a.subSkew g hg).transpose p r (Sum.inr i))
      (fun a i ↦ integrableOn_cutoff_mul_diagonalWeakState_readout _ t
        (a.subSkew g hg).transpose p r (Sum.inr i))
      (fun w hw i ↦ hInt.1 w hw (Sum.inr i)) (fun w hw i ↦ hInt.2 w hw (Sum.inr i))
      (fun i ↦ avsum_one_sub_cutoffAverage_mul_integral_childState_adjointSubSkew_eq_zero
        hstat hgrid hls hst hint g hg p r (Sum.inr i))
end
end HCPolySupport.HighContrast.Response
