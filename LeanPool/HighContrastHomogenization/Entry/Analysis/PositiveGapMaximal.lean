/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGap
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenCongruence
public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# High-contrast homogenization: Entry.Analysis.PositiveGapMaximal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weighted joint maxima for the positive gap

`p.two.grid.transport`. The finite maximum is retained in the random centered term;
only deterministic mean contributions are summed. Real nested suprema require
nonnegativity even for a nonempty finite family, because excluded indices
contribute `sSup ∅ = 0`.
-/
open HCPolySupport.HighContrast (CoeffSpace blockSub blockTrace)
namespace HCPolySupport.HighContrast.Analysis
open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder
noncomputable section

/-- A nonnegative finite family has the intended real nested supremum.
The hypothesis `∀ i ∈ I, 0 ≤ g i` cannot be dropped. That unrestricted statement
is false: take a proper singleton subset of `Bool` and `g` identically `-1`; the
excluded index contributes the empty real supremum `0`, while the finite supremum
is `-1`. This added premise is a correct strengthening: every consumer here
supplies nonnegative (Schatten/operator-norm) families. -/
theorem iSup_mem_finset_eq_finset_sup {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (g : ι → ℝ) (hg : ∀ i ∈ I, 0 ≤ g i) :
    (⨆ i ∈ (I : Set ι), g i) = I.sup' hI g := by
  classical
  obtain ⟨i, hi⟩ := id hI
  have h : ∃ i ∈ I, sSup (∅ : Set ℝ) ≤ g i := ⟨i, hi, by simpa using hg i hi⟩
  change (⨆ i ∈ I, g i) = _
  rw [Finset.ciSup_eq_max'_image g h (Finset.image_nonempty.mpr hI), Finset.sup'_eq_csSup_image,
    ← Finset.coe_image]
  exact (Finset.Nonempty.csSup_eq_max' (Finset.image_nonempty.mpr hI)).symm

private theorem memLp_finset_sup {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ENNReal} (I : Finset ι) (hI : I.Nonempty)
    (f : ι → α → ℝ) (hf : ∀ i ∈ I, MemLp (f i) p μ) :
    MemLp (fun a => I.sup' hI (fun i => f i a)) p μ := by
  classical
  induction I using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hI)
  | @insert i I hi ih =>
    by_cases hI' : I.Nonempty
    · have hfi := hf i (Finset.mem_insert_self _ _)
      have hfs := ih hI' (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sup'_insert hI', Pi.sup_apply] using! hfi.sup hfs
    · have hIe := Finset.not_nonempty_iff_eq_empty.mp hI'
      subst I
      simpa only [Finset.sup'_singleton] using! hf i (Finset.mem_singleton_self _)

/-- The maximum has a genuine finite moment; no totalized-integral shortcut is used. -/
theorem weightedMax_memLp {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ENNReal} (I : Finset ι) (hI : I.Nonempty) (f : ι → α → ℝ)
    (hf0 : ∀ i ∈ I, ∀ᵐ a ∂μ, 0 ≤ f i a) (hf : ∀ i ∈ I, MemLp (f i) p μ) :
    MemLp (fun a => ⨆ i ∈ (I : Set ι), f i a) p μ := by
  have heq : (fun a => I.sup' hI (fun i => f i a)) =ᵐ[μ]
      (fun a => ⨆ i ∈ (I : Set ι), f i a) := by
    filter_upwards [(Filter.eventually_all_finset I).mpr hf0] with a ha
    exact (iSup_mem_finset_eq_finset_sup I hI (fun i => f i a) ha).symm
  exact (memLp_congr_ae heq).mp (memLp_finset_sup I hI f hf)

/-- A nonempty joint maximum of nonnegative terms is nonnegative. -/
theorem weightedMax_nonneg {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (I : Finset ι) (hI
  : I.Nonempty) (f : ι → α → ℝ)
    (hf0 : ∀ i ∈ I, ∀ᵐ a ∂μ, 0 ≤ f i a) :
    ∀ᵐ a ∂μ, 0 ≤ ⨆ i ∈ (I : Set ι), f i a := by
  filter_upwards [(Filter.eventually_all_finset I).mpr hf0] with a ha
  rw [iSup_mem_finset_eq_finset_sup I hI _ ha]
  obtain ⟨i, hi⟩ := hI
  exact (ha i hi).trans (Finset.le_sup' (fun i => f i a) hi)

/-- An integrable nonnegative envelope has the expected root moment. -/
theorem weightedMax_root_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {N : ℝ} (hN : 0 < N) {t : α → ℝ} (ht : 0 ≤ᵐ[μ] t) (hint : Integrable t μ) :
    MemLp (fun a => t a ^ N⁻¹) (ENNReal.ofReal N) μ ∧
      (eLpNorm (fun a => t a ^ N⁻¹) (ENNReal.ofReal N) μ).toReal =
        (∫ a, t a ∂μ) ^ N⁻¹ := by
  have hn : 0 ≤ᵐ[μ] fun a => t a ^ N⁻¹ := ht.mono fun _ ha => Real.rpow_nonneg ha _
  have hm : AEStronglyMeasurable (fun a => t a ^ N⁻¹) μ :=
    (hint.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
  have hp : (fun a => (t a ^ N⁻¹) ^ N) =ᵐ[μ] t :=
    ht.mono fun _ ha => Real.rpow_inv_rpow ha hN.ne'
  have hmem : MemLp (fun a => t a ^ N⁻¹) (ENNReal.ofReal N) μ := by
    rw [← integrable_norm_rpow_iff hm (ne_of_gt (ENNReal.ofReal_pos.mpr hN))
      ENNReal.ofReal_ne_top]
    apply hint.congr
    filter_upwards [hn, hp] with a ha he
    simpa only [ENNReal.toReal_ofReal hN.le, Real.norm_of_nonneg ha] using he.symm
  exact ⟨hmem, (scalar_eLpNorm_toReal_eq_root hN hn hmem).trans
    (congrArg (fun x : ℝ => x ^ N⁻¹) (integral_congr_ae hp))⟩

private theorem mixed_root_eq {N s t : ℝ} (hN : 0 < N) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s ^ (N - 1) * t) ^ N⁻¹ = s ^ (1 - N⁻¹) * t ^ N⁻¹ := by
  rw [Real.mul_rpow (Real.rpow_nonneg hs _) ht, ← Real.rpow_mul hs]
  congr 2
  field_simp

private theorem full_sub {d : ℕ} (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext i j
  cases i <;> cases j <;> rfl

private theorem trace_sub {d : ℕ} (A B : BlockMat d) :
    blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
  exact congrArg Matrix.trace (full_sub A B) |>.trans (Matrix.trace_sub _ _)

/-- The printed mean-penalty conversion uses a positive natural moment.
The hypothesis `1 ≤ Q` cannot be dropped: without it the domination is false.
At `Q = 0`, with `d = 2` and `G = 2•I`, the right side is `0` while the left side
is `2`. This added premise is a correct strengthening; the real transport exponent
satisfies `bigQ ≥ 2`, so the actual consumer supplies `1 ≤ Q`. -/
theorem meanPenalty_mono_and_dominates (Q : ℕ) (hQ : 1 ≤ Q) {d : ℕ} {Pm G : BlockMat d} (hPm :
  IsSymmetricBlockMat Pm) (hG : IsSymmetricBlockMat G)
    (hI : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) Pm)
    (hPG : BlockMatLoewnerLE Pm G) :
    meanPenalty Q Pm ≤ meanPenalty Q G ∧
      blockOpNorm G ^ ((Q : ℝ) - 1) *
        blockTrace (blockSub G (Book.Ch02.blockIdentity d)) ≤ meanPenalty Q G := by
  have hIG := hI.trans hPG
  have hp0 := blockTrace_identity_sub_nonneg Pm hPm hI
  have hg0 := blockTrace_identity_sub_nonneg G hG hIG
  have ht : blockTrace (blockSub Pm (Book.Ch02.blockIdentity d)) ≤
      blockTrace (blockSub G (Book.Ch02.blockIdentity d)) := by
    have h := (Matrix.le_iff.mp (matrixOrder_of_blockMatLoewnerLE
      ((toFullBlockMat_isHermitian_iff _).mpr hPm)
      ((toFullBlockMat_isHermitian_iff _).mpr hG) hPG)).trace_nonneg
    rw [Matrix.trace_sub] at h; simp only [trace_sub]; exact sub_le_sub_right (sub_nonneg.mp h) _
  constructor
  · unfold meanPenalty
    exact sub_le_sub_right (pow_le_pow_left₀ (add_nonneg zero_le_one hp0)
      (add_le_add le_rfl ht) Q) 1
  · have hn := Annealed.blockOpNorm_le_one_add_trace G
      ((toFullBlockMat_isHermitian_iff _).mpr hG) hIG
    have hcast : (Q : ℝ) - 1 = ((Q - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hQ]; norm_num
    rw [hcast, Real.rpow_natCast]
    let t := blockTrace (blockSub G (Book.Ch02.blockIdentity d))
    have hp := pow_le_pow_left₀ (norm_nonneg (toFullBlockMat G)) hn (Q - 1)
    have hone : 1 ≤ (1 + t) ^ (Q - 1) := one_le_pow₀ (by linarith only [hg0])
    calc
      blockOpNorm G ^ (Q - 1) * t ≤ (1 + t) ^ (Q - 1) * t := mul_le_mul_of_nonneg_right hp hg0
      _ = (1 + t) ^ Q - (1 + t) ^ (Q - 1) := by
        conv_rhs => lhs; rw [← Nat.sub_add_cancel hQ, pow_succ]
        ring
      _ ≤ (1 + t) ^ Q - 1 := sub_le_sub_left hone _

private theorem root_const_mul_read {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {N k : ℝ} (hN : 0 < N) (hk : 0 ≤ k) {t : α → ℝ}
    (ht : 0 ≤ᵐ[μ] t) (hint : Integrable t μ) :
    (eLpNorm (fun a => k * t a ^ N⁻¹) (ENNReal.ofReal N) μ).toReal =
      k * (∫ a, t a ∂μ) ^ N⁻¹ := by
  have hmem := (weightedMax_root_memLp hN ht hint).1.const_mul k
  have hn := ht.mono fun _ ha => mul_nonneg hk (Real.rpow_nonneg ha N⁻¹)
  have he : (fun a => (k * t a ^ N⁻¹) ^ N) =ᵐ[μ] (fun a => k ^ N * t a) := by
    filter_upwards [ht] with a ha
    rw [Real.mul_rpow hk (Real.rpow_nonneg ha _), Real.rpow_inv_rpow ha hN.ne']
  rw [scalar_eLpNorm_toReal_eq_root hN hn hmem, integral_congr_ae he,
    integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hk _) (integral_nonneg_of_ae ht),
    Real.rpow_rpow_inv hk hN.ne']

private theorem scalar_joint_gap {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {N m : ℝ} (hN : 1 < N) (hm : 0 ≤ m) (I : Finset ι) (hI : I.Nonempty)
    (z s t : ι → α → ℝ) (hz0 : ∀ i ∈ I, ∀ᵐ a ∂μ, 0 ≤ z i a) (hs0 : ∀ i ∈ I, ∀ᵐ a ∂μ, 0 ≤ s i a)
      (ht0 : ∀ i ∈ I, ∀ᵐ a ∂μ, 0 ≤ t i a) (hz : ∀ i ∈ I, MemLp (z i) (ENNReal.ofReal N) μ)
    (hs : ∀ i ∈ I, MemLp (s i) (ENNReal.ofReal N) μ) (ht : ∀ i ∈ I, Integrable (t i) μ)
    (hpoint : ∀ i ∈ I, ∀ᵐ a ∂μ, z i a ≤ t i a ^ N⁻¹ +
      m ^ ((N - 1) / N ^ 2) * s i a ^ (1 - N⁻¹) * z i a ^ N⁻¹) :
    (∫ a, (⨆ i ∈ (I : Set ι), z i a) ^ N ∂μ) ^ N⁻¹ ≤
      m ^ N⁻¹ * (∫ a, (⨆ i ∈ (I : Set ι), s i a) ^ N ∂μ) ^ N⁻¹ +
        N / (N - 1) * (∑ i ∈ I, ∫ a, t i a ∂μ) ^ N⁻¹ := by
  let Z := fun a => ⨆ i ∈ (I : Set ι), z i a
  let S := fun a => ⨆ i ∈ (I : Set ι), s i a
  let T := fun a => ∑ i ∈ I, t i a
  have hN0 := zero_lt_one.trans hN
  have hr : 0 ≤ 1 - N⁻¹ := sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hN).le
  have hp := inv_nonneg.mpr hN0.le
  have hZ := weightedMax_memLp I hI z hz0 hz
  have hS := weightedMax_memLp I hI s hs0 hs
  have hZ0 := weightedMax_nonneg I hI z hz0
  have hS0 := weightedMax_nonneg I hI s hs0
  have hT : Integrable T μ := integrable_finsetSum _ ht
  have hT0 : 0 ≤ᵐ[μ] T := by
    filter_upwards [(Filter.eventually_all_finset I).mpr ht0] with a ha
    exact Finset.sum_nonneg (fun i hi => ha i hi)
  have hmix := (scalar_holder_power_integrable_bound hN hS0 hZ0 hS hZ).1
  have hmix0 := hS0.and hZ0 |>.mono fun _ h =>
    mul_nonneg (Real.rpow_nonneg h.1 (N - 1)) h.2
  have hu := weightedMax_root_memLp hN0 hT0 hT
  have hv := (weightedMax_root_memLp hN0 hmix0 hmix).1.const_mul (m ^ ((N - 1) / N ^ 2))
  have hcoef := Real.rpow_nonneg hm ((N - 1) / N ^ 2)
  have hdom : ∀ᵐ a ∂μ, ‖Z a‖ ≤
      ‖T a ^ N⁻¹ + m ^ ((N - 1) / N ^ 2) * (S a ^ (N - 1) * Z a) ^ N⁻¹‖ := by
    filter_upwards [(Filter.eventually_all_finset I).mpr hz0,
      (Filter.eventually_all_finset I).mpr hs0, (Filter.eventually_all_finset I).mpr ht0,
      (Filter.eventually_all_finset I).mpr hpoint, hZ0, hS0, hT0]
      with a hza hsa hta hpa hZa hSa hTa
    rw [Real.norm_of_nonneg hZa, Real.norm_of_nonneg (add_nonneg
      (Real.rpow_nonneg hTa _) (mul_nonneg hcoef
        (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hSa _) hZa) _))),
      mixed_root_eq hN0 hSa hZa]
    conv_lhs => rw [iSup_mem_finset_eq_finset_sup I hI _ hza]
    apply Finset.sup'_le hI _
    intro i hi
    have hzi : z i a ≤ Z a := by
      rw [show Z a = I.sup' hI (fun i => z i a) from iSup_mem_finset_eq_finset_sup I hI _ hza]
      exact Finset.le_sup' (fun i => z i a) hi
    have hsi : s i a ≤ S a := by
      rw [show S a = I.sup' hI (fun i => s i a) from iSup_mem_finset_eq_finset_sup I hI _ hsa]
      exact Finset.le_sup' (fun i => s i a) hi
    have hti : t i a ≤ T a := Finset.single_le_sum (fun j hj => hta j hj) hi
    apply (hpa i hi).trans
    apply add_le_add (Real.rpow_le_rpow (hta i hi) hti hp)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.rpow_le_rpow (hsa i hi) hsi hr)
        (Real.rpow_le_rpow (hza i hi) hzi hp) (Real.rpow_nonneg (hza i hi) _)
        (Real.rpow_nonneg hSa _)) hcoef
  have hsum := scalar_minkowski_toReal hN.le hu.1 hv
  have hnonlinear := (ENNReal.toReal_mono hsum.1.eLpNorm_ne_top
    (eLpNorm_mono_ae hZ.aestronglyMeasurable hdom)).trans hsum.2
  rw [hu.2, root_const_mul_read hN0 hcoef hmix0 hmix] at hnonlinear
  have hholder := scalar_mixedMoment_root_le hN hS0 hZ0 hS hZ
  have hnonlinear' : (eLpNorm Z (ENNReal.ofReal N) μ).toReal ≤
      (∫ a, T a ∂μ) ^ N⁻¹ + m ^ ((N - 1) / N ^ 2) *
        (eLpNorm S (ENNReal.ofReal N) μ).toReal ^ (1 - N⁻¹) *
          (eLpNorm Z (ENNReal.ofReal N) μ).toReal ^ N⁻¹ := by
    simpa only [mul_assoc] using hnonlinear.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      hholder hcoef))
  have habs := scalar_gap_young_absorb hN hm ENNReal.toReal_nonneg ENNReal.toReal_nonneg hnonlinear'
  rw [scalar_eLpNorm_toReal_eq_root hN0 hZ0 hZ,
    scalar_eLpNorm_toReal_eq_root hN0 hS0 hS, integral_finsetSum _ ht] at habs
  exact habs

private theorem weighted_root {N w c t : ℝ} (hN : 0 < N)
    (hw : 0 ≤ w) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    (w ^ N * c ^ (N - 1) * t) ^ N⁻¹ = w * c ^ (1 - N⁻¹) * t ^ N⁻¹ := by
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hw _) (Real.rpow_nonneg hc _)) ht,
    Real.mul_rpow (Real.rpow_nonneg hw _) (Real.rpow_nonneg hc _),
    Real.rpow_rpow_inv hw hN.ne', ← Real.rpow_mul hc]
  congr 3
  field_simp

private theorem weighted_mixed {N w s z : ℝ} (hw : 0 ≤ w) (hs : 0 ≤ s) (hz : 0 ≤ z) :
    (w * s) ^ (1 - N⁻¹) * (w * z) ^ N⁻¹ = w * (s ^ (1 - N⁻¹) * z ^ N⁻¹) := by
  rw [Real.mul_rpow hw hs, Real.mul_rpow hw hz]
  calc
    _ = (w ^ (1 - N⁻¹) * w ^ N⁻¹) * (s ^ (1 - N⁻¹) * z ^ N⁻¹) := by ring
    _ = _ := by rw [← Real.rpow_add' hw (by simp), sub_add_cancel, Real.rpow_one]

private theorem weighted_pointwise_gap {d : ℕ} {N : ℝ} (hN : 1 < N) {D G M : BlockMat d} (hD :
  (toFullBlockMat D).PosSemidef) (hG : (toFullBlockMat G).IsHermitian)
    (hM : (toFullBlockMat M).IsHermitian) (hDG : BlockMatLoewnerLE D G)
    {w : ℝ} (hw : 0 ≤ w) :
    w * absSchattenNorm N D ≤ (w ^ N * blockOpNorm M ^ (N - 1) * blockTrace D) ^ N⁻¹ +
      (2 * (d : ℝ)) ^ ((N - 1) / N ^ 2) *
        (w * absSchattenNorm N (blockSub G M)) ^ (1 - N⁻¹) * (w * absSchattenNorm N D) ^ N⁻¹ := by
  have hN0 := zero_lt_one.trans hN
  have hr : 0 ≤ 1 - N⁻¹ := sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hN).le
  have hp := inv_nonneg.mpr hN0.le
  have hC : (toFullBlockMat (blockSub G M)).IsHermitian := by rw [full_sub]; exact hG.sub hM
  have hs := absSchattenNorm_nonneg hC hN.le
  have hz := absSchattenNorm_nonneg hD.isHermitian hN.le
  have ht := blockTrace_nonneg hD
  have hc : 0 ≤ blockOpNorm M := norm_nonneg _
  have hm : 0 ≤ 2 * (d : ℝ) := by positivity
  have hop : blockOpNorm G ≤ blockOpNorm M + absSchattenNorm N (blockSub G M) := by
    calc
      _ ≤ blockOpNorm (blockSub G M) + blockOpNorm M := by
        simpa only [blockOpNorm, full_sub] using norm_le_norm_sub_add (toFullBlockMat G)
          (toFullBlockMat M)
      _ ≤ absSchattenNorm N (blockSub G M) + blockOpNorm M := add_le_add
        (blockOpNorm_le_absSchattenNorm (H := blockSub G M) hC hN.le) le_rfl
      _ = _ := add_comm _ _
  have htr := trace_le_dim_rpow_mul_absSchattenNorm hD hN.le
  have hgap : absSchattenNorm N D ≤ blockOpNorm M ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ +
      (2 * (d : ℝ)) ^ ((N - 1) / N ^ 2) *
        absSchattenNorm N (blockSub G M) ^ (1 - N⁻¹) * absSchattenNorm N D ^ N⁻¹ := by
    calc
      _ ≤ blockOpNorm G ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ :=
        absSchattenNorm_gap_le_opNorm_rpow_mul_trace_rpow hD hG hDG hN.le
      _ ≤ (blockOpNorm M + absSchattenNorm N (blockSub G M)) ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) hop hr) (Real.rpow_nonneg
        ht _)
      _ ≤ (blockOpNorm M ^ (1 - N⁻¹) + absSchattenNorm N (blockSub G M) ^ (1 - N⁻¹)) *
          blockTrace D ^ N⁻¹ := mul_le_mul_of_nonneg_right (scalar_gap_power_add_le hN.le hc hs)
            (Real.rpow_nonneg ht _)
      _ ≤ blockOpNorm M ^ (1 - N⁻¹) * blockTrace D ^ N⁻¹ +
          absSchattenNorm N (blockSub G M) ^ (1 - N⁻¹) *
            ((2 * (d : ℝ)) ^ (1 - N⁻¹) * absSchattenNorm N D) ^ N⁻¹ := by
        rw [add_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht htr hp)
          (Real.rpow_nonneg hs _))
      _ = _ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hm _) hz, ← Real.rpow_mul hm]
        have he : (1 - N⁻¹) * N⁻¹ = (N - 1) / N ^ 2 := by field_simp
        rw [he]; ring
  have hh := mul_le_mul_of_nonneg_left hgap hw
  rw [weighted_root hN0 hw hc ht, mul_assoc ((2 * (d : ℝ)) ^ ((N - 1) / N ^ 2)),
    weighted_mixed hw hs hz]
  simpa only [mul_add, mul_assoc, mul_left_comm, mul_comm] using hh

/-- Young absorption of the joint maximum; deterministic mean terms alone carry a sum. -/
theorem positiveGap_weighted_joint_absorbed {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {N : ℝ} (hN : 1 < N) {ι : Type*}
    (I : Finset ι) (hI : I.Nonempty) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (F G : ι → CoeffSpace d →
      BlockMat d) (hF : ∀ i ∈ I, SchattenMemLp P N (F i)) (hG : ∀ i ∈ I, SchattenMemLp P N (G i))
    (hFpos : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F i a))
    (hFG : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F i a) (G i a)) :
    let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
    let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
    (∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (G i a) (F i a))) ^ N ∂P) ^ N⁻¹ ≤
      (2 * (d : ℝ)) ^ N⁻¹ *
        (∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (G i a) (MG i))) ^ N ∂P) ^ N⁻¹ +
      N / (N - 1) * (∑ i ∈ I, w i ^ N * blockOpNorm (MG i) ^ (N - 1) *
        blockTrace (blockSub (MG i) (MF i))) ^ N⁻¹ := by
  dsimp only
  let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
  let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
  let D := fun i a => blockSub (G i a) (F i a)
  let z := fun i a => w i * absSchattenNorm N (D i a)
  let s := fun i a => w i * absSchattenNorm N (blockSub (G i a) (MG i))
  let t := fun i a => w i ^ N * blockOpNorm (MG i) ^ (N - 1) * blockTrace (D i a)
  have hd (i) (hi : i ∈ I) := positiveGap_ordered_data hN.le (hF i hi) (hG i hi) (hFpos i hi)
    (hFG i hi)
  have hc (i) (hi : i ∈ I) := (hG i hi).center hN.le
  have hz0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ z i a := by
    intro i hi
    filter_upwards [(hd i hi).2.1] with a ha
    exact mul_nonneg (hw i) (absSchattenNorm_nonneg ha.1.isHermitian hN.le)
  have hs0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ s i a := by
    intro i hi
    filter_upwards [(hc i hi).symmetric] with a ha
    exact mul_nonneg (hw i) (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN.le)
  have ht0 : ∀ i ∈ I, ∀ᵐ a ∂P, 0 ≤ t i a := by
    intro i hi
    filter_upwards [(hd i hi).2.1] with a ha
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hw i) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) (blockTrace_nonneg ha.1)
  have hint (i) (hi : i ∈ I) := blockTrace_integral ((hd i hi).1.integrable_entry hN.le)
  have hpoint : ∀ i ∈ I, ∀ᵐ a ∂P, z i a ≤ t i a ^ N⁻¹ +
      (2 * (d : ℝ)) ^ ((N - 1) / N ^ 2) * s i a ^ (1 - N⁻¹) * z i a ^ N⁻¹ := by
    intro i hi
    filter_upwards [(hd i hi).2.1, (hG i hi).symmetric] with a ha hga
    exact weighted_pointwise_gap hN ha.1 ((toFullBlockMat_isHermitian_iff _).2 hga) (hd i
      hi).2.2.2.2.1.isHermitian ha.2 (hw i)
  have h := scalar_joint_gap hN (by positivity : 0 ≤ 2 * (d : ℝ)) I hI z s t hz0 hs0 ht0
    (fun i hi => ((hd i hi).1.memLp_absSchattenNorm hN.le).const_mul (w i))
    (fun i hi => ((hc i hi).memLp_absSchattenNorm hN.le).const_mul (w i))
    (fun i hi => (hint i hi).1.const_mul _) hpoint
  have he : (∑ i ∈ I, ∫ a, t i a ∂P) = ∑ i ∈ I, w i ^ N * blockOpNorm (MG i) ^ (N - 1) *
      blockTrace (blockSub (MG i) (MF i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [t]; rw [integral_const_mul, ← (hint i hi).2, (hd i hi).2.2.1]
  rw [he] at h; exact h

private theorem weighted_schatten_data {d : ℕ} {P : Measure (CoeffSpace d)} {N w : ℝ}
    (hN : 1 ≤ N) (hw : 0 ≤ w) {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P N H) :
    (∀ᵐ a ∂P, 0 ≤ w * absSchattenNorm N (H a)) ∧
      MemLp (fun a => w * absSchattenNorm N (H a)) (ENNReal.ofReal N) P := by
  exact ⟨hH.symmetric.mono fun _ ha => mul_nonneg hw
    (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN),
    (hH.memLp_absSchattenNorm hN).const_mul w⟩

private theorem root_le_add_const {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {N c : ℝ} (hN : 1 ≤ N) (hc : 0 ≤ c) {u f g : α → ℝ}
    (hu0 : 0 ≤ᵐ[μ] u) (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) (hu : MemLp u (ENNReal.ofReal N) μ)
      (hf : MemLp f (ENNReal.ofReal N) μ)
    (hg : MemLp g (ENNReal.ofReal N) μ) (h : ∀ᵐ a ∂μ, u a ≤ f a + g a + c) :
    (∫ a, u a ^ N ∂μ) ^ N⁻¹ ≤ (∫ a, f a ^ N ∂μ) ^ N⁻¹ + (∫ a, g a ^ N ∂μ) ^ N⁻¹ + c := by
  have hN0 := zero_lt_one.trans_le hN
  have hsum := scalar_minkowski_toReal hN hf hg
  have hsum' := scalar_minkowski_toReal hN hsum.1 (memLp_const c)
  have hdom : ∀ᵐ a ∂μ, ‖u a‖ ≤ ‖f a + g a + c‖ := by
    filter_upwards [hu0, hf0, hg0, h] with a hua hfa hga ha
    simpa only [Real.norm_of_nonneg hua, Real.norm_of_nonneg (add_nonneg (add_nonneg hfa hga)
      hc)] using ha
  have hconst : (eLpNorm (fun _ : α => c) (ENNReal.ofReal N) μ).toReal = c := by
    rw [scalar_eLpNorm_toReal_eq_root hN0 (ae_of_all μ (fun _ => hc)) (memLp_const c)]
    simpa only [integral_const, probReal_univ, one_smul] using Real.rpow_rpow_inv hc hN0.ne'
  rw [← scalar_eLpNorm_toReal_eq_root hN0 hu0 hu, ← scalar_eLpNorm_toReal_eq_root hN0 hf0 hf,
    ← scalar_eLpNorm_toReal_eq_root hN0 hg0 hg]
  exact (ENNReal.toReal_mono hsum'.1.eLpNorm_ne_top
    (eLpNorm_mono_ae hu.aestronglyMeasurable hdom)).trans (hsum'.2.trans (by
      rw [hconst]; exact add_le_add hsum.2 le_rfl))

/-- `p.two.grid.transport`: the full weighted joint-maximum positive gap. -/
theorem positiveGap_weighted_joint_max (d : ℕ)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {N : ℝ} (hN : 2 ≤ N)
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (F G : ι → CoeffSpace d → BlockMat d) (hF : ∀ i ∈ I, SchattenMemLp P N (F i)) (hG : ∀ i ∈ I,
      SchattenMemLp P N (G i)) (hFpos : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0)
      (F i a))
    (hFG : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F i a) (G i a)) :
    let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
    let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
    (∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (F i a) (MF i))) ^ N ∂P) ^ N⁻¹ ≤
      (1 + (2 * (d : ℝ)) ^ N⁻¹) *
        (∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (G i a) (MG i))) ^ N ∂P) ^ N⁻¹ +
      2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * (∑ i ∈ I, w i ^ N * blockOpNorm (MG i) ^ (N - 1) *
        blockTrace (blockSub (MG i) (MF i))) ^ N⁻¹ := by
  dsimp only
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hNlt : 1 < N := (by norm_num : (1 : ℝ) < 2).trans_le hN
  have hN0 := zero_lt_one.trans hNlt
  let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
  let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
  let f := fun i a => w i * absSchattenNorm N (blockSub (F i a) (MF i))
  let g := fun i a => w i * absSchattenNorm N (blockSub (G i a) (MG i))
  let z := fun i a => w i * absSchattenNorm N (blockSub (G i a) (F i a))
  let b := fun i => w i ^ N * blockOpNorm (MG i) ^ (N - 1) * blockTrace (blockSub (MG i) (MF i))
  let B := (∑ i ∈ I, b i) ^ N⁻¹
  let c := (2 * (d : ℝ)) ^ (1 - N⁻¹) * B
  have hd (i) (hi : i ∈ I) := positiveGap_ordered_data hN1 (hF i hi) (hG i hi) (hFpos i hi) (hFG
    i hi)
  have hm (i) (hi : i ∈ I) := positiveGap_mean_gap_bounds hN1 (hF i hi) (hG i hi) (hFpos i hi)
    (hFG i hi)
  have hb (i) (hi : i ∈ I) : 0 ≤ b i := mul_nonneg (mul_nonneg (Real.rpow_nonneg (hw i) _)
    (Real.rpow_nonneg (norm_nonneg _) _)) (hm i hi).1
  have hB : 0 ≤ B := Real.rpow_nonneg (Finset.sum_nonneg hb) _
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by positivity) _) hB
  have hfd (i) (hi : i ∈ I) := weighted_schatten_data hN1 (hw i) ((hF i hi).center hN1)
  have hgd (i) (hi : i ∈ I) := weighted_schatten_data hN1 (hw i) ((hG i hi).center hN1)
  have hzd (i) (hi : i ∈ I) := weighted_schatten_data hN1 (hw i) (hd i hi).1
  have hdet (i) (hi : i ∈ I) : w i * absSchattenNorm N (blockSub (MG i) (MF i)) ≤ c := by
    have hh := mul_le_mul_of_nonneg_left ((hm i hi).2.1.trans (hm i hi).2.2.2) (hw i)
    have hbi : b i ^ N⁻¹ ≤ B := Real.rpow_le_rpow (hb i hi) (Finset.single_le_sum hb hi)
      (inv_nonneg.mpr hN0.le)
    have he : w i * ((2 * (d : ℝ)) ^ (1 - N⁻¹) * blockOpNorm (MG i) ^ (1 - N⁻¹) *
        blockTrace (blockSub (MG i) (MF i)) ^ N⁻¹) = (2 * (d : ℝ)) ^ (1 - N⁻¹) * b i ^ N⁻¹ := by
      dsimp only [b]; rw [weighted_root hN0 (hw i) (c := blockOpNorm (MG i)) (t := blockTrace
        (blockSub (MG i) (MF i))) (norm_nonneg _) (hm i hi).1]; ring
    exact (hh.trans_eq he).trans (mul_le_mul_of_nonneg_left hbi (Real.rpow_nonneg (by
      positivity) _))
  have hpoint : ∀ i ∈ I, ∀ᵐ a ∂P, f i a ≤ g i a + z i a + c := by
    intro i hi
    filter_upwards [((hG i hi).center hN1).symmetric, (hd i hi).2.1] with a hga hda
    have hGc := (toFullBlockMat_isHermitian_iff _).2 hga
    have hM := (hd i hi).2.2.2.2.2.1.isHermitian
    have hDM : (toFullBlockMat (blockSub (blockSub (G i a) (F i a)) (blockSub (MG i) (MF
      i)))).IsHermitian := by
      rw [full_sub]; exact hda.1.isHermitian.sub hM
    have ht := (absSchattenNorm_sub_le hGc hDM hN1).trans (add_le_add le_rfl
      (absSchattenNorm_sub_le hda.1.isHermitian hM hN1))
    rw [← positiveGap_centered_identity] at ht; exact (mul_le_mul_of_nonneg_left ht (hw i)).trans
      (by simpa only [mul_add, add_assoc, g, z, MG] using add_le_add (add_le_add (le_refl (g i
        a)) (le_refl (z i a))) (hdet i hi))
  have hmax : ∀ᵐ a ∂P, (⨆ i ∈ (I : Set ι), f i a) ≤
      (⨆ i ∈ (I : Set ι), g i a) + (⨆ i ∈ (I : Set ι), z i a) + c := by
    filter_upwards [(Filter.eventually_all_finset I).mpr (fun i hi => (hfd i hi).1),
      (Filter.eventually_all_finset I).mpr (fun i hi => (hgd i hi).1),
      (Filter.eventually_all_finset I).mpr (fun i hi => (hzd i hi).1),
      (Filter.eventually_all_finset I).mpr hpoint] with a hfa hga hza ha
    rw [iSup_mem_finset_eq_finset_sup I hI _ hfa, iSup_mem_finset_eq_finset_sup I hI _ hga,
      iSup_mem_finset_eq_finset_sup I hI _ hza]
    exact Finset.sup'_le hI _ fun i hi => (ha i hi).trans (add_le_add
      (add_le_add (Finset.le_sup' (fun i => g i a) hi) (Finset.le_sup' (fun i => z i a) hi)) le_rfl)
  have hroot := root_le_add_const hN1 hc
    (weightedMax_nonneg I hI f (fun i hi => (hfd i hi).1))
    (weightedMax_nonneg I hI g (fun i hi => (hgd i hi).1))
    (weightedMax_nonneg I hI z (fun i hi => (hzd i hi).1))
    (weightedMax_memLp I hI f (fun i hi => (hfd i hi).1) (fun i hi => (hfd i hi).2))
    (weightedMax_memLp I hI g (fun i hi => (hgd i hi).1) (fun i hi => (hgd i hi).2))
    (weightedMax_memLp I hI z (fun i hi => (hzd i hi).1) (fun i hi => (hzd i hi).2)) hmax
  have hy := positiveGap_weighted_joint_absorbed hNlt I hI w hw F G hF hG hFpos hFG
  have hcoef : N / (N - 1) + (2 * (d : ℝ)) ^ (1 - N⁻¹) ≤ 2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) := by
    calc
      _ ≤ 2 + 2 * (d : ℝ) ^ (1 - N⁻¹) := add_le_add (scalar_gap_absorption_factor_le_two hN)
        (scalar_gap_dimension_factor_le hN1 (Nat.cast_nonneg d))
      _ = _ := by ring
  calc
    _ ≤ _ := hroot
    _ ≤ (∫ a, (⨆ i ∈ (I : Set ι), g i a) ^ N ∂P) ^ N⁻¹ +
        ((2 * (d : ℝ)) ^ N⁻¹ * (∫ a, (⨆ i ∈ (I : Set ι), g i a) ^ N ∂P) ^ N⁻¹ +
          N / (N - 1) * B) + c := add_le_add (add_le_add le_rfl hy) le_rfl
    _ = (1 + (2 * (d : ℝ)) ^ N⁻¹) * (∫ a, (⨆ i ∈ (I : Set ι), g i a) ^ N ∂P) ^ N⁻¹ +
        (N / (N - 1) + (2 * (d : ℝ)) ^ (1 - N⁻¹)) * B := by dsimp only [c]; ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hB)

private theorem weightedMax_opNorm_moment_le {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} (hN : 1 ≤ N) {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (H : ι → CoeffSpace d → BlockMat d)
    (hH : ∀ i ∈ I, SchattenMemLp P N (H i)) :
    Integrable (fun a => (⨆ i ∈ (I : Set ι), w i * blockOpNorm (H i a)) ^ N) P ∧
      (∫ a, (⨆ i ∈ (I : Set ι), w i * blockOpNorm (H i a)) ^ N ∂P) ≤
        ∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (H i a)) ^ N ∂P := by
  have hN0 := zero_lt_one.trans_le hN
  have hs (i) (hi : i ∈ I) := weighted_schatten_data hN (hw i) (hH i hi)
  let f := fun i a => w i * blockOpNorm (H i a)
  let g := fun i a => w i * absSchattenNorm N (H i a)
  have hf0 (i) (_hi : i ∈ I) : ∀ᵐ a ∂P, 0 ≤ f i a := ae_of_all P fun _ => mul_nonneg (hw i)
    (norm_nonneg _)
  have hfg (i) (hi : i ∈ I) : ∀ᵐ a ∂P, f i a ≤ g i a := (hH i hi).symmetric.mono fun _ ha =>
    mul_le_mul_of_nonneg_left (blockOpNorm_le_absSchattenNorm (H := H i _)
      ((toFullBlockMat_isHermitian_iff _).2 ha) hN) (hw i)
  have hf (i) (hi : i ∈ I) : MemLp (f i) (ENNReal.ofReal N) P := by
    have hm : AEMeasurable (fun a => toFullBlockMat (H i a)) P :=
      AEMeasurable.of_eval fun α => AEMeasurable.of_eval fun β => ((hH i hi).measurable α
        β).aemeasurable
    apply (hs i hi).2.mono' (hm.norm.const_mul (w i)).aestronglyMeasurable
    filter_upwards [hfg i hi, hf0 i hi] with a ha hfa
    change ‖f i a‖ ≤ g i a
    rwa [Real.norm_of_nonneg hfa]
  have hmF := weightedMax_memLp I hI f hf0 hf
  have hmG := weightedMax_memLp I hI g (fun i hi => (hs i hi).1) (fun i hi => (hs i hi).2)
  have hF0 := weightedMax_nonneg I hI f hf0
  have hG0 := weightedMax_nonneg I hI g (fun i hi => (hs i hi).1)
  have hint {u : CoeffSpace d → ℝ} (hu : MemLp u (ENNReal.ofReal N) P) (hu0 : 0 ≤ᵐ[P] u) :
      Integrable (fun a => u a ^ N) P := by
    apply (hu.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hN0))
      ENNReal.ofReal_ne_top).congr
    filter_upwards [hu0] with a ha
    simp only [Real.norm_of_nonneg ha, ENNReal.toReal_ofReal hN0.le]
  refine ⟨hint hmF hF0, integral_mono_ae (hint hmF hF0) (hint hmG hG0) ?_⟩
  filter_upwards [(Filter.eventually_all_finset I).mpr hf0,
    (Filter.eventually_all_finset I).mpr (fun i hi => (hs i hi).1),
    (Filter.eventually_all_finset I).mpr hfg, hF0] with a hfa hga ha hFa
  apply Real.rpow_le_rpow hFa _ hN0.le
  rw [iSup_mem_finset_eq_finset_sup I hI _ hfa, iSup_mem_finset_eq_finset_sup I hI _ hga]
  exact Finset.sup'_le hI _ fun i hi => (ha i hi).trans (Finset.le_sup' (fun i => g i a) hi)

private theorem power_two_terms {N x y a b : ℝ} (hN : 1 ≤ N) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * x ^ N⁻¹ + b * y ^ N⁻¹) ^ N ≤ 2 ^ (N - 1) * (a ^ N * x + b ^ N * y) := by
  have hN0 := zero_lt_one.trans_le hN
  have hh := NNReal.rpow_add_le_mul_rpow_add_rpow
    ⟨a * x ^ N⁻¹, mul_nonneg ha (Real.rpow_nonneg hx _)⟩
    ⟨b * y ^ N⁻¹, mul_nonneg hb (Real.rpow_nonneg hy _)⟩ hN
  have hr : (a * x ^ N⁻¹ + b * y ^ N⁻¹) ^ N ≤
      2 ^ (N - 1) * ((a * x ^ N⁻¹) ^ N + (b * y ^ N⁻¹) ^ N) := by exact_mod_cast hh
  rwa [Real.mul_rpow ha (Real.rpow_nonneg hx _), Real.mul_rpow hb (Real.rpow_nonneg hy _),
    Real.rpow_inv_rpow hx hN0.ne', Real.rpow_inv_rpow hy hN0.ne'] at hr

/-- `p.two.grid.transport`: the weighted extension of the fixed-target power estimate at
with the operator norm on the left. -/
theorem positiveGap_weighted_joint_max_pow (d : ℕ)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {N : ℝ} (hN : 2 ≤ N)
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (F G : ι → CoeffSpace d → BlockMat d) (hF : ∀ i ∈ I, SchattenMemLp P N (F i)) (hG : ∀ i ∈ I,
      SchattenMemLp P N (G i)) (hFpos : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0)
      (F i a))
    (hFG : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (F i a) (G i a)) :
    let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
    let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
    (∫ a, (⨆ i ∈ (I : Set ι), w i * blockOpNorm (blockSub (F i a) (MF i))) ^ N ∂P) ≤
      2 ^ (N - 1) * (1 + (2 * (d : ℝ)) ^ N⁻¹) ^ N *
        (∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (G i a) (MG i))) ^ N ∂P) +
      2 ^ (2 * N - 1) * (1 + (d : ℝ) ^ (1 - N⁻¹)) ^ N *
        ∑ i ∈ I, w i ^ N * blockOpNorm (MG i) ^ (N - 1) * blockTrace (blockSub (MG i) (MF i)) := by
  dsimp only
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hN0 := zero_lt_one.trans_le hN1
  let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
  let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
  let X := ∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (F i a) (MF i))) ^ N ∂P
  let Y := ∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm N (blockSub (G i a) (MG i))) ^ N ∂P
  let B := ∑ i ∈ I, w i ^ N * blockOpNorm (MG i) ^ (N - 1) * blockTrace (blockSub (MG i) (MF i))
  have hX : 0 ≤ X := integral_nonneg_of_ae <| (weightedMax_nonneg I hI _
    (fun i hi => (weighted_schatten_data hN1 (hw i) ((hF i hi).center hN1)).1)).mono fun _ ha =>
      Real.rpow_nonneg ha _
  have hY : 0 ≤ Y := integral_nonneg_of_ae <| (weightedMax_nonneg I hI _
    (fun i hi => (weighted_schatten_data hN1 (hw i) ((hG i hi).center hN1)).1)).mono fun _ ha =>
      Real.rpow_nonneg ha _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i hi => mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (hw i) _) (Real.rpow_nonneg (norm_nonneg _) _))
    (positiveGap_mean_gap_bounds hN1 (hF i hi) (hG i hi) (hFpos i hi) (hFG i hi)).1
  have hA : 0 ≤ 1 + (2 * (d : ℝ)) ^ N⁻¹ := by positivity
  have hD : 0 ≤ 1 + (d : ℝ) ^ (1 - N⁻¹) := by positivity
  have hbound := positiveGap_weighted_joint_max d hN I hI w hw F G hF hG hFpos hFG
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hX N⁻¹) hbound hN0.le
  rw [Real.rpow_inv_rpow hX hN0.ne'] at hpow
  have htwo := power_two_terms hN1 hY hB hA (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
  have hcoef : (2 : ℝ) ^ (N - 1) * 2 ^ N = 2 ^ (2 * N - 1) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  calc
    _ ≤ X := (weightedMax_opNorm_moment_le hN1 I hI w hw _ (fun i hi => (hF i hi).center hN1)).2
    _ ≤ _ := hpow
    _ ≤ _ := htwo
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD, ← hcoef]
      dsimp only [Y, B, MF, MG]; ring

/-- A finite target maximum pays the target count after taking moments.
The proof records integrability of the actual maximum and every moment. -/
theorem transport_target_max_moment {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} {N : ℝ} (hN : 0 < N) (Z : Finset ι) (hZ : Z.Nonempty)
    (f : ι → α → ℝ) (hf0 : ∀ z ∈ Z, ∀ᵐ a ∂P, 0 ≤ f z a)
    (hf : ∀ z ∈ Z, MemLp (f z) (ENNReal.ofReal N) P) :
    Integrable (fun a => (⨆ z ∈ (Z : Set ι), f z a) ^ N) P ∧
      (∫ a, (⨆ z ∈ (Z : Set ι), f z a) ^ N ∂P) ≤ ∑ z ∈ Z, ∫ a, f z a ^ N ∂P := by
  have hint {g : α → ℝ} (hg : MemLp g (ENNReal.ofReal N) P) (hg0 : ∀ᵐ a ∂P, 0 ≤ g a) :
      Integrable (fun a => g a ^ N) P := by
    apply (hg.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hN))
      ENNReal.ofReal_ne_top).congr
    filter_upwards [hg0] with a ha
    simp only [Real.norm_of_nonneg ha, ENNReal.toReal_ofReal hN.le]
  have hmax := weightedMax_memLp Z hZ f hf0 hf
  have hmax0 : ∀ᵐ a ∂P, 0 ≤ ⨆ z ∈ (Z : Set ι), f z a := by
    filter_upwards [(Filter.eventually_all_finset Z).mpr hf0] with a ha
    rw [iSup_mem_finset_eq_finset_sup Z hZ _ ha]
    obtain ⟨z, hz⟩ := hZ
    exact (ha z hz).trans (Finset.le_sup' (fun z => f z a) hz)
  refine ⟨hint hmax hmax0, ?_⟩
  rw [← integral_finsetSum _ (fun z hz => hint (hf z hz) (hf0 z hz))]
  apply integral_mono_ae (hint hmax hmax0)
    (integrable_finsetSum _ (fun z hz => hint (hf z hz) (hf0 z hz)))
  filter_upwards [(Filter.eventually_all_finset Z).mpr hf0] with a ha
  rw [iSup_mem_finset_eq_finset_sup Z hZ _ ha]
  obtain ⟨z, hz, he⟩ := Finset.exists_mem_eq_sup' hZ (fun z => f z a)
  rw [he]
  exact Finset.single_le_sum (fun i hi => Real.rpow_nonneg (ha i hi) N) hz

/-- A common L^N envelope stays under the joint maximum without an index-count
loss. Both sides are genuine integrable moments. -/
theorem transport_joint_envelope_moment {α ι : Type*} [MeasurableSpace α]
    {P : Measure α} {N B : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (Z : Finset ι) (hZ : Z.Nonempty) (f : ι → α → ℝ) (hf0 : ∀ z ∈ Z, ∀ᵐ a ∂P, 0 ≤ f z a) (hf : ∀
      z ∈ Z, MemLp (f z) (ENNReal.ofReal N) P)
    (X : α → ℝ) (hX0 : ∀ᵐ a ∂P, 0 ≤ X a) (hX : MemLp X (ENNReal.ofReal N) P)
    (hbound : ∀ z ∈ Z, ∀ᵐ a ∂P, f z a ≤ B * X a) :
    Integrable (fun a => (⨆ z ∈ (Z : Set ι), f z a) ^ N) P ∧
      (∫ a, (⨆ z ∈ (Z : Set ι), f z a) ^ N ∂P) ≤ B ^ N * ∫ a, X a ^ N ∂P := by
  have hmax := (transport_target_max_moment hN Z hZ f hf0 hf).1
  have hXM : Integrable (fun a => X a ^ N) P := by
    apply (hX.integrable_norm_rpow (ne_of_gt (ENNReal.ofReal_pos.mpr hN))
      ENNReal.ofReal_ne_top).congr
    filter_upwards [hX0] with a ha
    simp only [Real.norm_of_nonneg ha, ENNReal.toReal_ofReal hN.le]
  refine ⟨hmax, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae hmax (hXM.const_mul (B ^ N))
  filter_upwards [(Filter.eventually_all_finset Z).mpr hf0,
    (Filter.eventually_all_finset Z).mpr hbound, hX0] with a ha hb hxa
  rw [iSup_mem_finset_eq_finset_sup Z hZ _ ha, ← Real.mul_rpow hB hxa]
  obtain ⟨z, hz⟩ := hZ
  have hZ : Z.Nonempty := ⟨z, hz⟩
  have hmax0 : 0 ≤ Z.sup' hZ (fun z => f z a) := (ha z hz).trans (Finset.le_sup' (fun z : ι => f
    z a) hz)
  exact Real.rpow_le_rpow hmax0 (Finset.sup'_le hZ _ hb) hN.le

end
end HCPolySupport.HighContrast.Analysis
