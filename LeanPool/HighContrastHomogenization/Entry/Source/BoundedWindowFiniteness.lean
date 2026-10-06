/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedLocality
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Source.AdaptedBound
public import LeanPool.HighContrastHomogenization.Entry.Source.Multiplier

/-!
# High-contrast homogenization: Entry.Source.BoundedWindowFiniteness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Bounded-window source moments

`p.fixed.geometry.parent.child.recurrence`, plan B4. The auxiliary source window is separate from
the
consumer's fixed rounded grid. Each finite real exponent uses a fresh sufficiently
high source moment. Only finiteness is asserted; the fixed-Q uniform bound is not reused.
-/

open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace annealedBlock blockMatEntry_blockScale blockScale
  blockTrace coarseBlock isSymmetricBlockMat_coarseBlockMatrix matSqrt measurable_translateCoeff
  normalizedBlock toFullBlockMat_eq_blockMatEntry translateCoeff)
open HCPolySupport.HighContrast (adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace HCPolySupport.HighContrast.Source
open scoped Matrix.Norms.L2Operator
open Set MeasureTheory Filter Geometry
noncomputable section

/-- Every finite moment of a characterized source minimum exists on any fixed auxiliary
window. This repeats the tail argument with a new source moment and asserts no uniform
norm bound at the new exponent. The consumer's rounded grid is not changed. -/
theorem source_minimum_memLp_all {d : ℕ} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hdag : CoarseEllipticityDagger P γ E Ψ K S) (jWindow : ℕ)
    (ell : CoeffSpace d → ℕ) (X : CoeffSpace d → ℝ)
    (hell : Measurable ell) (hX : Measurable X)
    (hform : ∀ a, X a = (3 : ℝ) ^ (γ * (ell a : ℝ)))
    (htail : ∀ p : ℝ, 1 ≤ p → ∀ r : ℕ,
      P.real {a | r < ell a} ≤
        (3 : ℝ) ^ (d * jWindow) * (∫ a, S a ^ p ∂P) /
          ((3 : ℝ) ^ (jWindow + r)) ^ p) :
    ∀ N : ℝ, 1 ≤ N → MemLp X (ENNReal.ofReal N) P ∧ Integrable (fun a => X a ^ N) P := by
  intro N hN
  let p : ℝ := γ * N + 1
  have hp : 1 ≤ p := by
    dsimp [p]
    have hN0 : 0 ≤ N := le_trans zero_le_one hN
    linarith only [mul_nonneg hdag.g_mem.1 hN0]
  obtain ⟨C, hC, hsource⟩ := CoarseEllipticityDagger.source_moment_bound p hp
  have hI := (hsource P γ E Ψ K S hdag).2.2
  let b : ℝ := (3 : ℝ) ^ (γ * N)
  let q : ℝ := (3 : ℝ) ^ (-p)
  let A : ℝ := C * K ^ C / (3 : ℝ) ^ ((p - (d : ℝ)) * (jWindow : ℝ))
  have hK : 0 < K := zero_lt_one.trans hdag.one_lt_growthWitness
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbq : b * q < 1 := by
    dsimp [b, q]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    dsimp [p]
    linarith only []
  have hden : 0 < 1 - b * q := sub_pos.mpr hbq
  have ht (r : ℕ) : P.real {a | r < ell a} ≤ A * q ^ r := by
    calc
      _ ≤ _ := htail p hp r
      _ ≤ (3 : ℝ) ^ (d * jWindow) * (C * K ^ C) / ((3 : ℝ) ^ (jWindow + r)) ^ p := by gcongr
      _ = _ := source_tail_power_identity d jWindow r p (C * K ^ C)
  have hsum := stopping_lintegral_le P ell hell b A q hb hA hq hbq ht
  have hpow (a : CoeffSpace d) : X a ^ N = b ^ ell a := by
    rw [hform a]
    dsimp [b]
    simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hX0 (a : CoeffSpace d) : 0 ≤ X a := by rw [hform a]; positivity
  have hn : 0 ≤ᵐ[P] (fun a => X a ^ N) := ae_of_all _ (fun a => Real.rpow_nonneg (hX0 a) N)
  have hfin : (∫⁻ a, ENNReal.ofReal (X a ^ N) ∂P) ≠ ⊤ := by
    simp_rw [hpow]
    exact ne_of_lt (hsum.trans_lt ENNReal.ofReal_lt_top)
  have hi : Integrable (fun a => X a ^ N) P :=
    (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const N).aestronglyMeasurable hn).1 hfin
  refine ⟨?_, hi⟩
  apply (integrable_norm_rpow_iff hX.aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans_le hN)) ENNReal.ofReal_ne_top).1
  simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hN), Real.norm_eq_abs,
    abs_of_nonneg (hX0 _)] using hi

/-- On any auxiliary source window the attained minimum has every finite moment.
No source threshold or change to a consumer's rounded metric is required. -/
theorem source_minimum_all_moments {d : ℕ} (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jWindow : ℕ) :
    let Good : ℕ → CoeffSpace d → Prop := fun r a => ∀ w : Fin d → ℤ,
      standardCellCenter ((jWindow + r : ℕ) : ℤ) w ∈
        centeredCube d ((2 * jWindow + r : ℕ) : ℤ) →
      S (translateCoeff (fun i => (3 : ℤ) ^ (jWindow + r) * w i) a) ≤
        (3 : ℝ) ^ (jWindow + r)
    ∃ (ell : CoeffSpace d → ℕ) (X : CoeffSpace d → ℝ),
      Measurable ell ∧ Measurable X ∧
      (∀ a, X a = (3 : ℝ) ^ (γ * (ell a : ℝ))) ∧
      (∀ a, ¬ (∃ r, Good r a) → ell a = 0) ∧
      (∀ᵐ a ∂P, Good (ell a) a ∧
        (∀ r, Good r a → ell a ≤ r) ∧
        (∀ r, Good r a → X a ≤ (3 : ℝ) ^ (γ * (r : ℝ)))) ∧
      (γ = 0 → ∀ a, X a = 1) ∧
      (∀ N : ℝ, 1 ≤ N → MemLp X (ENNReal.ofReal N) P ∧
        Integrable (fun a => X a ^ N) P) := by
  intro Good
  obtain ⟨ell, X, hell, hX, hform, hdefault, hmin, hzero, htail⟩ :=
    source_minimum P γ E Ψ K S hstat hdag jWindow
  exact ⟨ell, X, hell, hX, hform, hdefault, hmin, hzero,
    source_minimum_memLp_all P γ E Ψ K S hdag jWindow ell X hell hX hform htail⟩

/-- Every bounded region fits in an auxiliary centered source window. The window
is independent of a consumer's fixed rounded grid and of any source threshold. -/
theorem exists_auxiliary_source_window {d : ℕ} {W : Set (Vec d)}
    (hW : Bornology.IsBounded W) :
    ∃ J : ℕ, W ⊆ centeredCube d (2 * (J : ℤ)) := by
  obtain ⟨R, hR, hbound⟩ := hW.exists_pos_norm_le
  obtain ⟨J, hJ⟩ := exists_nat_gt (Real.logb 3 (2 * R))
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hp : 2 * R < (3 : ℝ) ^ (2 * (J : ℤ)) := by
    calc
      2 * R = (3 : ℝ) ^ Real.logb 3 (2 * R) :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ < (3 : ℝ) ^ (2 * (J : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith only [hJ, hJ0])
      _ = _ := by rw [← Real.rpow_intCast]; norm_cast
  refine ⟨J, fun x hx => ?_⟩
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have hxnorm : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hi : |x i| ≤ R := hxnorm.trans (hbound x hx)
  obtain ⟨hl, hu⟩ := abs_le.mp hi
  constructor
  · linarith only [hp, hl]
  · linarith only [hp, hu]

/-- A bounded region has one measurable source envelope with every finite real
moment, simultaneously for all adapted cells with the rounded inverse bound.
The auxiliary scale is proof data and asserts no uniform norm bound. -/
theorem bounded_source_envelope {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (W : Set (Vec d)) (hW : Bornology.IsBounded W) :
    ∃ (J : ℕ) (X : CoeffSpace d → ℝ), Measurable X ∧ (∀ a, 0 ≤ X a) ∧
      (∀ N : ℝ, 1 ≤ N → MemLp X (ENNReal.ofReal N) P) ∧
      (∀ᵐ a ∂P, ∀ (q : Mat d), InverseNormLE q 2 → ∀ (j : ℤ) (y : Vec d),
        adaptedCellTranslate q j y ⊆ W →
        BlockMatLoewnerLE (coarseBlock (adaptedCellTranslate q j y) a)
          (blockScale ((12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
            X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)) E)) := by
  obtain ⟨J, hwindow⟩ := exists_auxiliary_source_window hW
  obtain ⟨ell, X, _, hX, hform, _, hmin, _, hmoments⟩ :=
    source_minimum_all_moments P γ E Ψ K S hstat hdag J
  have hX0 (a : CoeffSpace d) : 0 ≤ X a := by rw [hform]; positivity
  refine ⟨J, X, hX, hX0, fun N hN => (hmoments N hN).1, ?_⟩
  filter_upwards [hmin, stationary_all_integer_dagger_event hstat hdag] with a ha hcoarse
  have hstd (k : ℤ) (w : Fin d → ℤ)
      (hw : standardCell d k w ⊆ centeredCube d (2 * (J : ℤ))) :
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale (X a * (3 : ℝ) ^ (γ * max ((J : ℝ) - (k : ℝ)) 0)) E) := by
    rw [hform]
    exact source_standard_multiplier_bound γ E hdag.g_mem.1 hdag.refBlock_posDef S a
      J (ell a) hcoarse ha.1 k w hw
  intro q hq j y hcell
  exact adapted_bound_of_standard γ hdag.g_mem E hdag.refBlock_posDef a J
    (X a) (hX0 a) hstd hq j y (hcell.trans hwindow)

/-- An integrable scalar order envelope supplies Schatten membership after
measurability and full spectral positivity have been established. -/
theorem memLqSchatten_of_order_envelope {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} (hN : 1 ≤ N) {A : CoeffSpace d → BlockMat d} {E : BlockMat d}
    (hAm : HasMeasurableBlock P A)
    (hAs : ∀ᵐ a ∂P, IsSymmetricBlockMat (A a))
    (hAp : ∀ᵐ a ∂P, Book.Ch02.BlockPosDef (A a))
    {X : CoeffSpace d → ℝ} (hX : MemLp X (ENNReal.ofReal N) P) (D : ℝ)
    (horder : ∀ᵐ a ∂P, BlockMatLoewnerLE (A a) (blockScale (D * X a) E)) :
    SchattenMemLp P N A := by
  have hsm := Analysis.aestronglyMeasurable_absSchattenNorm hAm hN
  have hscalar : MemLp (fun a => absSchattenNorm N (A a)) (ENNReal.ofReal N) P := by
    apply (hX.const_mul (D * blockTrace E)).mono' hsm
    filter_upwards [hAs, hAp, horder] with a hs hp ho
    have hpsd := fullBlock_posSemidef_of_pos hs hp
    rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.absSchattenNorm_nonneg hpsd.isHermitian hN)]
    calc
      absSchattenNorm N (A a) ≤ blockTrace (A a) := Analysis.absSchattenNorm_le_blockTrace hpsd hN
      _ ≤ blockTrace (blockScale (D * X a) E) := blockTrace_le_of_order ho
      _ = (D * blockTrace E) * X a := by
        simp only [blockTrace, Matrix.trace, Matrix.diag, toFullBlockMat_eq_blockMatEntry,
          blockMatEntry_blockScale, ← Finset.mul_sum]
        ring
  refine ⟨hAm, hAs, ?_⟩
  have hi := (integrable_norm_rpow_iff hsm
    (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans_le hN)) ENNReal.ofReal_ne_top).2 hscalar
  apply hi.congr
  filter_upwards [hAs] with a hs
  simp only [Real.norm_eq_abs, abs_of_nonneg
    (Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff _).2 hs) hN),
    ENNReal.toReal_ofReal (zero_le_one.trans hN)]

/-- Bounded-window generalized finiteness for every finite real moment. The proof
chooses its own auxiliary source window and moment; it needs neither the original
source containment nor its fixed-Q threshold, and gives no new uniform norm bound. -/
theorem memLqSchatten_coarseBlock_adapted (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) (y : Vec d)
    (N : ℝ) (hN : 1 ≤ N) :
    SchattenMemLp P N
      (fun a => coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) a) := by
  let : NeZero d := ⟨by omega⟩
  let q := explicitRoundedGrid jStar m
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  let W := adaptedCellTranslate q j y
  have hW : Bornology.IsBounded W := by
    dsimp [W]
    rw [Annealed.adaptedCellTranslate_eq_cg_affine]
    exact (isOpenBoundedConvexDomain_affine_openCube q hq j y).isBoundedDomain.isBounded
  obtain ⟨J, X, _, _, hXN, hbound⟩ := bounded_source_envelope P γ E Ψ K S hstat hdag W hW
  have hmeas : HasMeasurableBlock P (fun a => coarseBlock W a) := fun α β =>
    ((Annealed.measurable_coarseBlock_entry_adapted q hq j y α β).mono
      (Annealed.coeffSigma_le_global _) le_rfl).aestronglyMeasurable
  let D : ℝ := (12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
    (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0)
  apply memLqSchatten_of_order_envelope hN hmeas
    (ae_of_all _ (fun a => isSymmetricBlockMat_coarseBlockMatrix W (⇑a.1)))
    (ae_of_all _ (fun a => Annealed.blockPosDef_coarseBlock_adapted q hq j y a)) (hXN N hN) D
  filter_upwards [hbound] with a ha
  have hb := ha q (inverseNormLE_roundedGrid hj hm) j y Subset.rfl
  convert hb using 1
  congr 1
  dsimp [D]
  ring

/-- Deterministic full-matrix congruence preserves finite Schatten membership.
No annealed identity or positivity normalization is used. -/
theorem memLqSchatten_congruence {d : ℕ} {P : Measure (CoeffSpace d)} {N : ℝ}
    {A : CoeffSpace d → BlockMat d} (hA : SchattenMemLp P N A) (hN : 1 ≤ N)
    (B : FullBlockMat d) :
    SchattenMemLp P N (fun a => ofFullBlockMat (B.conjTranspose * toFullBlockMat (A a) * B)) := by
  have hm : AEMeasurable (fun a => toFullBlockMat (A a)) P :=
    AEMeasurable.of_eval (fun α => AEMeasurable.of_eval (fun β =>
      (hA.measurable α β).aemeasurable))
  have hc : AEMeasurable (fun a => B.conjTranspose * toFullBlockMat (A a) * B) P :=
    (aemeasurable_const.mul hm).mul aemeasurable_const
  have hcm : HasMeasurableBlock P (fun a => ofFullBlockMat (B.conjTranspose * toFullBlockMat (A
    a) * B)) := by
    intro α β
    simpa only [blockMatEntry_ofFullBlockMat] using!
      ((measurable_pi_apply β).comp_aemeasurable
        ((measurable_pi_apply α).comp_aemeasurable hc)).aestronglyMeasurable
  have hcs : ∀ᵐ a ∂P, IsSymmetricBlockMat (ofFullBlockMat (B.conjTranspose * toFullBlockMat (A
    a) * B)) := by
    filter_upwards [hA.symmetric] with a ha
    apply (Analysis.toFullBlockMat_isHermitian_iff _).1
    rw [toFullBlockMat_ofFullBlockMat]
    exact Matrix.isHermitian_conjTranspose_mul_mul B ((Analysis.toFullBlockMat_isHermitian_iff
      _).2 ha)
  apply memLqSchatten_of_norm_envelope hN hcm hcs (hA.memLp_absSchattenNorm hN) (‖B‖ ^ 2)
  filter_upwards [hA.symmetric] with a ha
  have hh := (Analysis.toFullBlockMat_isHermitian_iff _).2 ha
  simp only [blockOpNorm, toFullBlockMat_ofFullBlockMat]
  calc
    _ ≤ (‖B.conjTranspose‖ * ‖toFullBlockMat (A a)‖) * ‖B‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (‖B‖ * blockOpNorm (A a)) * ‖B‖ := by rw [show B.conjTranspose = star B from rfl,
      norm_star]; rfl
    _ ≤ (‖B‖ * absSchattenNorm N (A a)) * ‖B‖ := by
      gcongr
      exact Analysis.blockOpNorm_le_absSchattenNorm hh hN
    _ = _ := by ring

/-- The deterministic inverse-square-root normalization preserves
membership. The root's total definition is symmetric even at its junk branch;
a source consumer may in particular take any positive reference block R. -/
theorem memLqSchatten_normalizedBlock {d : ℕ} {P : Measure (CoeffSpace d)} {N : ℝ}
    {A : CoeffSpace d → BlockMat d} (hA : SchattenMemLp P N A) (hN : 1 ≤ N)
    (R : BlockMat d) : SchattenMemLp P N (fun a => normalizedBlock (A a) R) := by
  have hr : (matSqrt ((toFullBlockMat R)⁻¹)).IsHermitian := by
    unfold matSqrt
    split_ifs with h
    · exact h.choose_spec.1.isHermitian
    · exact Matrix.isHermitian_one
  have hc := memLqSchatten_congruence hA hN (matSqrt ((toFullBlockMat R)⁻¹))
  simpa only [hr.eq, normalizedBlock] using hc

/-- Every deterministic finite weighted sum of Schatten members is a member.
The empty family is included, and the dimension factor proves finiteness only. -/
theorem memLqSchatten_finset_sum {d : ℕ} {ι : Type*} {P : Measure (CoeffSpace d)} {N : ℝ}
    (hN : 1 ≤ N) (s : Finset ι) (w : ι → ℝ) (A : ι → CoeffSpace d → BlockMat d)
    (hA : ∀ i ∈ s, SchattenMemLp P N (A i)) :
    SchattenMemLp P N (fun a => ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat (A i a))) := by
  classical
  let X := fun a => ∑ i ∈ s, |w i| * absSchattenNorm N (A i a)
  have hX : MemLp X (ENNReal.ofReal N) P := memLp_finsetSum s (fun i hi =>
    ((hA i hi).memLp_absSchattenNorm hN).const_mul |w i|)
  have hm : HasMeasurableBlock P (fun a => ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat (A i
    a))) := by
    intro α β
    simp only [blockMatEntry_ofFullBlockMat, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, toFullBlockMat_eq_blockMatEntry]
    have h := s.aestronglyMeasurable_sum (fun i hi => ((hA i hi).measurable α β).const_mul (w i))
    convert h using 1
    funext a
    simp
  have hs : ∀ᵐ a ∂P, ∀ i ∈ s, IsSymmetricBlockMat (A i a) := by
    have hs' : ∀ᵐ a ∂P, ∀ i : s, IsSymmetricBlockMat (A i a) :=
      eventually_countable_forall.mpr (fun i => (hA i i.2).symmetric)
    exact hs'.mono (fun a ha i hi => ha ⟨i, hi⟩)
  have hsym : ∀ᵐ a ∂P, IsSymmetricBlockMat (ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat (A i
    a))) := by
    filter_upwards [hs] with a ha
    intro α β
    simp only [blockMatEntry_ofFullBlockMat, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, toFullBlockMat_eq_blockMatEntry]
    exact Finset.sum_congr rfl (fun i hi => by rw [ha i hi α β])
  apply memLqSchatten_of_norm_envelope hN hm hsym hX 1
  filter_upwards [hs] with a ha
  simp only [blockOpNorm, toFullBlockMat_ofFullBlockMat, one_mul]
  calc
    _ ≤ ∑ i ∈ s, ‖w i • toFullBlockMat (A i a)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, |w i| * blockOpNorm (A i a) := by simp only [norm_smul, Real.norm_eq_abs,
      blockOpNorm]
    _ ≤ X a := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (Analysis.blockOpNorm_le_absSchattenNorm ((Analysis.toFullBlockMat_isHermitian_iff _).2
        (ha i hi)) hN)
      (abs_nonneg _))

/-- S2 integer stationarity identifies the actual entrywise annealed means.
This uses only measurable transport and does not assume annealed normalization. -/
theorem annealedBlock_adapted_add_intTranslation {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) (z : Fin d → ℤ) :
    annealedBlock P (adaptedCellTranslate q j (y + HCPolySupport.Source.AKL.intTranslation z)) =
      annealedBlock P (adaptedCellTranslate q j y) := by
  have he (α β : BlockCoord d) :
      (∫ a, blockMatEntry (coarseBlock (adaptedCellTranslate q j (y +
        HCPolySupport.Source.AKL.intTranslation z)) a) α β ∂P) =
        ∫ a, blockMatEntry (coarseBlock (adaptedCellTranslate q j y) a) α β ∂P := by
    have hm := (Annealed.measurable_coarseBlock_entry_adapted q hq j y α β).mono
      (Annealed.coeffSigma_le_global _) le_rfl
    have hi := integral_map (μ := P) (measurable_translateCoeff z).aemeasurable
      hm.aestronglyMeasurable
    rw [hstat z] at hi
    calc
      _ = ∫ a, blockMatEntry (coarseBlock (adaptedCellTranslate q j y) (translateCoeff z a)) α β
        ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ (fun a => congrArg (fun A => blockMatEntry A α β)
          (Annealed.coarseBlock_adapted_translateCoeff q j y z a).symm)
      _ = _ := hi.symm
  have hentry (U : Set (Vec d)) (α β : BlockCoord d) :
      blockMatEntry (annealedBlock P U) α β = ∫ a, blockMatEntry (coarseBlock U a) α β ∂P := by
    cases α <;> cases β <;> rfl
  apply (show Function.Injective (toFullBlockMat (d := d)) from
    Function.LeftInverse.injective ofFullBlockMat_toFullBlockMat)
  ext α β
  rw [toFullBlockMat_eq_blockMatEntry, toFullBlockMat_eq_blockMatEntry, hentry, hentry]
  exact he α β

end
end HCPolySupport.HighContrast.Source
