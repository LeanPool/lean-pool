/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.GaussianMaximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TranslationCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.TwoTermTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.HalfScaleExponentBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.ProductPower
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.ConcentrationAEMeasurable

/-!
# ObservationScaleFiniteCoverDepth

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Internal deterministic depth transport for the observation-scale cover

This module contains only the deterministic multiscale inequalities used by
`ObservationScaleFiniteCover`.  It is separated to keep each Lean file focused
and below the repository line limit.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverInternal

open Filter MeasureTheory Set
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Deterministic depth transport -/

def weightedDepthEnergySq (s : ℝ) (H : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, Ch02.geometricWeight s 2 n * H n

private theorem summable_geometricWeight_mul_of_profile_bound
    {s C : ℝ} {H : ℕ → ℝ} (hs : 0 < s)
    (hH0 : ∀ n, 0 ≤ H n) (hHC : ∀ n, H n ≤ C) :
    Summable (fun n : ℕ => Ch02.geometricWeight s 2 n * H n) :=
  HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
    (by positivity : 0 < s * (2 : ℝ)) hH0 hHC

private theorem profileAtDepth_le_rpow_mul_weightedDepthEnergySq
    {s C : ℝ} {H : ℕ → ℝ} (hs : 0 < s)
    (hH0 : ∀ n, 0 ≤ H n) (hmono : Monotone H)
    (hHC : ∀ n, H n ≤ C) (N : ℕ) :
    H N ≤ Real.rpow 3 (2 * s * (N : ℝ)) * weightedDepthEnergySq s H := by
  let w : ℕ → ℝ := fun n => Ch02.geometricWeight s 2 n
  let T : ℕ → ℝ := fun n => H (n + N)
  have hsum : Summable (fun n : ℕ => w n * H n) := by
    simpa only [w] using summable_geometricWeight_mul_of_profile_bound hs hH0 hHC
  have hTmono : Monotone T := fun i j hij => hmono (Nat.add_le_add_right hij N)
  have hT0 : ∀ n, 0 ≤ T n := fun n => hH0 (n + N)
  have hTC : ∀ n, T n ≤ C := fun n => hHC (n + N)
  have hTsum : Summable (fun n : ℕ => w n * T n) := by
    simpa only [w] using summable_geometricWeight_mul_of_profile_bound hs hT0 hTC
  have hself : T 0 ≤ ∑' n : ℕ, w n * T n :=
    HCPolySupport.self_le_tsum_geometricWeight_of_monotone
      hTmono (by positivity : 0 < s * (2 : ℝ)) hTsum
  have htail_nonneg : 0 ≤ ∑' n : ℕ, w (n + N) * H (n + N) :=
    tsum_nonneg fun n => mul_nonneg
      (HCPolySupport.geometricWeight_nonneg
        (n + N) (by positivity : 0 ≤ s * (2 : ℝ)))
      (hH0 (n + N))
  have hprefix_nonneg : 0 ≤ ∑ n ∈ Finset.range N, w n * H n :=
    Finset.sum_nonneg fun n _ => mul_nonneg
      (HCPolySupport.geometricWeight_nonneg
        n (by positivity : 0 ≤ s * (2 : ℝ)))
      (hH0 n)
  have hsplit :
      (∑ n ∈ Finset.range N, w n * H n) +
          ∑' n : ℕ, w (n + N) * H (n + N) =
        ∑' n : ℕ, w n * H n := by
    simpa only [Nat.add_comm] using hsum.sum_add_tsum_nat_add N
  have htail : (∑' n : ℕ, w (n + N) * H (n + N)) ≤ ∑' n : ℕ, w n * H n := by
    linarith
  have hshift :
      (∑' n : ℕ, w n * T n) =
        Real.rpow 3 (2 * s * (N : ℝ)) *
          ∑' n : ℕ, w (n + N) * H (n + N) := by
    calc
      (∑' n : ℕ, w n * T n) =
          ∑' n : ℕ, Real.rpow 3 (2 * s * (N : ℝ)) *
            (w (n + N) * H (n + N)) := by
        apply tsum_congr
        intro n
        dsimp only [w, T]
        have hweight : Ch02.geometricWeight s 2 n =
            Real.rpow 3 (s * 2 * (N : ℝ)) * Ch02.geometricWeight s 2 (n + N) := by
          simpa only [Ch02.geometricWeight_eq_old] using
            (HCPolySupport.geometricWeight_shift (s := s) (q := 2) N n)
        rw [hweight]
        ring_nf
      _ = Real.rpow 3 (2 * s * (N : ℝ)) *
          ∑' n : ℕ, w (n + N) * H (n + N) := tsum_mul_left
  have hfac0 : 0 ≤ Real.rpow 3 (2 * s * (N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    H N = T 0 := by simp [T]
    _ ≤ ∑' n : ℕ, w n * T n := hself
    _ = Real.rpow 3 (2 * s * (N : ℝ)) *
        ∑' n : ℕ, w (n + N) * H (n + N) := hshift
    _ ≤ Real.rpow 3 (2 * s * (N : ℝ)) * ∑' n : ℕ, w n * H n :=
      mul_le_mul_of_nonneg_left htail hfac0
    _ = Real.rpow 3 (2 * s * (N : ℝ)) * weightedDepthEnergySq s H := rfl

private theorem monotone_maxDescendantNormalizedBlockResponse_depth
    (Q : HCPolySupport.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (a0 : HCPolySupport.Mat d) :
    Monotone (fun n : ℕ => Ch02.maxDescendantNormalizedBlockResponseAtScale
      Q (Q.scale - (n : ℤ)) a a0) := by
  intro i j hij
  have hijz : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
  exact Ch02.maxDescendantNormalizedBlockResponseAtScale_le_of_le Q
    (by omega) (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le i)) a a0

/-- A response at depth `N` is controlled by the squared lower-discount
homogenization error on its root, with the exact `q = 2` depth factor. -/
theorem maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
    (Q : HCPolySupport.TriadicCube d) {s : ℝ} (hs : 0 < s)
    (a : Ch02.TriadicCoeffFamily d) (a0 : HCPolySupport.Mat d) (N : ℕ) :
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (N : ℤ)) a a0 ≤
      Real.rpow 3 (2 * s * (N : ℝ)) *
        (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 := by
  let H : ℕ → ℝ := fun n => Ch02.maxDescendantNormalizedBlockResponseAtScale
    Q (Q.scale - (n : ℤ)) a a0
  have hH0 : ∀ n, 0 ≤ H n := fun n =>
    Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)) a a0
  have hmono : Monotone H := by
    simpa only [H] using monotone_maxDescendantNormalizedBlockResponse_depth Q a a0
  have hHC : ∀ n, H n ≤ Ch02.normalizedBlockResponseUniformBound Q a a0 := fun n =>
    Ch02.maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
      (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le n)) a a0
  have hexpose := profileAtDepth_le_rpow_mul_weightedDepthEnergySq
    hs hH0 hmono hHC N
  have hsq := Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0
  simpa only [H, weightedDepthEnergySq, Ch02.geometricWeight_eq_old, hsq] using hexpose

omit [NeZero d] in
private theorem exists_mem_descendantsAtDepth_add
    {Q S : HCPolySupport.TriadicCube d} {j n : ℕ}
    (hS : S ∈ descendantsAtDepth Q (j + n)) :
    ∃ R ∈ descendantsAtDepth Q j, S ∈ descendantsAtDepth R n := by
  induction n generalizing S with
  | zero => exact ⟨S, by simpa using hS, by simp⟩
  | succ n ih =>
      rw [show j + (n + 1) = (j + n) + 1 from rfl,
        mem_descendantsAtDepth_succ_iff] at hS
      obtain ⟨T, hT, hchild⟩ := hS
      obtain ⟨R, hR, hTR⟩ := ih hT
      exact ⟨R, hR, mem_descendantsAtDepth_succ_iff.2 ⟨T, hTR, hchild⟩⟩

omit [NeZero d] in
theorem exists_mem_descendantsAtScale_split
    {Q S : HCPolySupport.TriadicCube d} {k l : ℤ}
    (hk : k ≤ Q.scale) (hl : l ≤ k) (hS : S ∈ descendantsAtScale Q l) :
    ∃ R ∈ descendantsAtScale Q k, S ∈ descendantsAtScale R l := by
  have hlQ : l ≤ Q.scale := hl.trans hk
  have hsplit : Int.toNat (Q.scale - l) =
      Int.toNat (Q.scale - k) + Int.toNat (k - l) := by omega
  rw [descendantsAtScale_eq_descendantsAtDepth Q hlQ, hsplit] at hS
  obtain ⟨R, hR, hSR⟩ := exists_mem_descendantsAtDepth_add hS
  have hRmem : R ∈ descendantsAtScale Q k := by
    rwa [descendantsAtScale_eq_descendantsAtDepth Q hk]
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hRmem
  refine ⟨R, hRmem, ?_⟩
  rw [descendantsAtScale_eq_descendantsAtDepth R (by rw [hRscale]; exact hl),
    show Int.toNat (R.scale - l) = Int.toNat (k - l) by rw [hRscale]]
  exact hSR

/-- Subadditivity turns one normalized parent response into the average of the
same normalized response over any fixed descendant generation. -/
theorem normalizedBlockResponseMax_le_descendantsAverage
    (Q : HCPolySupport.TriadicCube d) (j : ℕ)
    (a : Ch02.TriadicCoeffFamily d) (a0 : HCPolySupport.Mat d) :
    Ch02.normalizedBlockResponseMax Q a a0 ≤
      descendantsAverage Q j (fun R => Ch02.normalizedBlockResponseMax R a a0) := by
  classical
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hk : Q.scale - (j : ℤ) ≤ Q.scale :=
    sub_le_self Q.scale (by exact_mod_cast Nat.zero_le j)
  have hcell : ∀ i : Pcell.Cell,
      Ch02.CoeffOn.RestrictsTo (a.coeffOn Q) (a.coeffOn i.1) := by
    intro i
    exact a.restrictsTo_descendant hk (by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      have hdepth : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
        rw [sub_sub_cancel]
        exact_mod_cast Int.toNat_of_nonneg
          (show (0 : ℤ) ≤ (j : ℤ) by exact_mod_cast Nat.zero_le j)
      rw [hdepth]
      exact i.2)
  unfold Ch02.normalizedBlockResponseMax
  refine csSup_le (Ch02.normalizedBlockResponseValueSet_nonempty Q a a0) ?_
  rintro x ⟨e, he, rfl⟩
  let P := _root_.HCPolySupport.ofFullBlockVec
    (Matrix.mulVec (Ch02.constantFullBlockMatrixInvSqrt a0) e)
  let Q' := _root_.HCPolySupport.ofFullBlockVec
    (Matrix.mulVec (Ch02.constantFullBlockMatrixSqrt a0) e)
  let F : HCPolySupport.TriadicCube d → ℝ := fun R =>
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R)
      (P.1 - Q'.2) (Q'.1 - P.2)
  let G : HCPolySupport.TriadicCube d → ℝ := fun R =>
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R).transpose
      (Q'.2 + P.1) (Q'.1 + P.2)
  have hrespF :
      Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
          (P.1 - Q'.2) (Q'.1 - P.2) ≤ descendantsAverage Q j F := by
    have hsub :=
      (Ch02.responseSubadditivityAndScalingTheory
        (Ch02.cubeDomain Q) (a.coeffOn Q)).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => a.coeffOn i.1) hcell
        (P.1 - Q'.2) (Q'.1 - P.2)
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
          (P.1 - Q'.2) (Q'.1 - P.2) ≤
          Pcell.weightedAverage (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (a.coeffOn i.1)
              (P.1 - Q'.2) (Q'.1 - P.2)) := by
        simpa [Pcell, Ch02.descendantsDomainPartition] using hsub
      _ = descendantsAverage Q j F := by
        simpa [Pcell, F] using
          Ch02.descendantsDomainPartition_weightedAverage Q j F
  have hrespG :
      Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q).transpose
          (Q'.2 + P.1) (Q'.1 + P.2) ≤ descendantsAverage Q j G := by
    have hcellT : ∀ i : Pcell.Cell,
        Ch02.CoeffOn.RestrictsTo (a.coeffOn Q).transpose
          (a.coeffOn i.1).transpose := fun i => (hcell i).transpose
    have hsub :=
      (Ch02.responseSubadditivityAndScalingTheory
        (Ch02.cubeDomain Q) (a.coeffOn Q).transpose).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => (a.coeffOn i.1).transpose) hcellT
        (Q'.2 + P.1) (Q'.1 + P.2)
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q).transpose
          (Q'.2 + P.1) (Q'.1 + P.2) ≤
          Pcell.weightedAverage (fun i : Pcell.Cell =>
            Ch02.responseJ (Ch02.cubeDomain i.1) (a.coeffOn i.1).transpose
              (Q'.2 + P.1) (Q'.1 + P.2)) := by
        simpa [Pcell, Ch02.descendantsDomainPartition] using hsub
      _ = descendantsAverage Q j G := by
        simpa [Pcell, G] using
          Ch02.descendantsDomainPartition_weightedAverage Q j G
  have hcombine :
      (1 / 2 : ℝ) * descendantsAverage Q j F +
          (1 / 2 : ℝ) * descendantsAverage Q j G =
        descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
    calc
      (1 / 2 : ℝ) * descendantsAverage Q j F +
          (1 / 2 : ℝ) * descendantsAverage Q j G =
          descendantsAverage Q j (fun R => (1 / 2 : ℝ) * F R) +
            descendantsAverage Q j (fun R => (1 / 2 : ℝ) * G R) := by
        rw [descendantsAverage_smul, descendantsAverage_smul]
      _ = descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
        symm
        exact descendantsAverage_add Q j _ _
  have hresp : Ch02.doubledResponseJ (Ch02.cubeDomain Q) (a.coeffOn Q) P Q' ≤
      descendantsAverage Q j
        (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := by
    calc
      Ch02.doubledResponseJ (Ch02.cubeDomain Q) (a.coeffOn Q) P Q' =
          (1 / 2 : ℝ) * Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q)
              (P.1 - Q'.2) (Q'.1 - P.2) +
            (1 / 2 : ℝ) * Ch02.responseJ (Ch02.cubeDomain Q)
              (a.coeffOn Q).transpose (Q'.2 + P.1) (Q'.1 + P.2) := by
        simpa [P, Q'] using
          (Ch02.doubledResponseTheory
            (Ch02.cubeDomain Q) (a.coeffOn Q)).doubledResponseJ_eq_scalar
            P.1 Q'.2 P.2 Q'.1
      _ ≤ (1 / 2 : ℝ) * descendantsAverage Q j F +
          (1 / 2 : ℝ) * descendantsAverage Q j G := by nlinarith
      _ = descendantsAverage Q j
          (fun R => (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R) := hcombine
  have hpointwise : ∀ R ∈ descendantsAtDepth Q j,
      (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R ≤
        Ch02.normalizedBlockResponseMax R a a0 := by
    intro R hR
    have hmem : (1 / 2 : ℝ) * F R + (1 / 2 : ℝ) * G R ∈
        Ch02.normalizedBlockResponseValueSet R a a0 := by
      refine ⟨e, he, ?_⟩
      dsimp [F, G, P, Q']
      exact ((Ch02.doubledResponseTheory
        (Ch02.cubeDomain R) (a.coeffOn R)).doubledResponseJ_eq_scalar
        P.1 Q'.2 P.2 Q'.1).symm
    unfold Ch02.normalizedBlockResponseMax
    have hRk : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
      have hdepth : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by
        rw [sub_sub_cancel]
        exact_mod_cast Int.toNat_of_nonneg
          (show (0 : ℤ) ≤ (j : ℤ) by exact_mod_cast Nat.zero_le j)
      rw [hdepth]
      exact hR
    exact le_csSup
      (Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
        (a := a) (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) a0 hRk) hmem
  exact hresp.trans (descendantsAverage_le_descendantsAverage Q j hpointwise)


end

end Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverInternal
