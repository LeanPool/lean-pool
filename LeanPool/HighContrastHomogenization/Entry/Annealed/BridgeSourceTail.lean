/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.ReferenceNormalization
public import LeanPool.HighContrastHomogenization.Entry.Geometry.BridgeEccentricity

/-!
# High-contrast homogenization: Entry.Annealed.BridgeSourceTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The fine source tail for the two-grid bridge

Near `e.two.grid.whitney.source`, `p.successful.short.bridge`. The fine generations are indexed by
their
nonnegative deficit below `jStar - 1`; no generation is truncated away.
The geometric ratio is `3 ^ (-(1-γ))`, strictly below one for `γ < 1`.

The normalization has no reference-order premise.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockMatEntry_blockScale
  blockScale blockTrace coarseBlock isSymmetricBlockMat_coarseBlockMatrix
  toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate centeredCube)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory Geometry Filter
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- The exact fine geometric ratio is nonnegative and strictly less than one. -/
theorem bridge_fine_ratio_mem_Ico {γ : ℝ} (hγ : γ < 1) :
    (3 : ℝ) ^ (-(1 - γ)) ∈ Set.Ico (0 : ℝ) 1 := by
  refine ⟨Real.rpow_nonneg (by norm_num) _, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])

/-- Any countable fine family with the Whitney row estimate has the summable
source penalty. The summable unweighted masses come from disjointness in the
finite-volume parent; the row estimate is supplied by the two-grid bridge. -/
theorem bridge_fine_weighted_sum {ι : Type*}
    (w : ι → ℝ) (r : ι → ℤ) (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (J j : ℤ) (hr : ∀ i, r i < J) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ t : ℤ, (∑' i : {i // r i = t}, w i) ≤ C * (3 : ℝ) ^ ((t : ℝ) - j))
    (γ : ℝ) (hγ : γ < 1) :
    Summable (fun i => w i * (3 : ℝ) ^ (γ * ((J : ℝ) - r i))) ∧
      (∑' i, w i * (3 : ℝ) ^ (γ * ((J : ℝ) - r i))) ≤
        C / (1 - (3 : ℝ) ^ (-(1 - γ))) * (3 : ℝ) ^ (-((j : ℝ) - J)) := by
  classical
  let f := fun i => w i * (3 : ℝ) ^ (γ * ((J : ℝ) - r i))
  let deficit := fun i => (J - 1 - r i).toNat
  let F := fun n : ℕ => {i // deficit i = n}
  let ρ := (3 : ℝ) ^ (-(1 - γ))
  let D := C * (3 : ℝ) ^ (-((j : ℝ) - J))
  have hρ := bridge_fine_ratio_mem_Ico hγ
  have hf0 (i) : 0 ≤ f i := mul_nonneg (hw0 i) (Real.rpow_nonneg (by norm_num) _)
  have hgen (n : ℕ) (i : F n) : r i = J - 1 - (n : ℤ) := by
    have hh : ((J - 1 - r i).toNat : ℤ) = (n : ℤ) := by exact_mod_cast i.2
    rw [Int.toNat_of_nonneg (by have := hr i; omega)] at hh
    omega
  have heq (n : ℕ) (i : F n) : f i =
      w i * (3 : ℝ) ^ (γ * ((n : ℝ) + 1)) := by
    dsimp only [f]
    rw [hgen n i]
    push_cast
    congr 2
    ring
  have hrows (n : ℕ) : Summable (fun i : F n => f i) ∧
      (∑' i : F n, f i) ≤ D * ρ ^ n := by
    have hwF : Summable (fun i : F n => w i) := hw.subtype _
    have hsum : Summable (fun i : F n => f i) := by
      simp_rw [heq n]
      exact hwF.mul_right _
    refine ⟨hsum, ?_⟩
    have hmass : (∑' i : F n, w i) ≤ C * (3 : ℝ) ^ ((J : ℝ) - 1 - n - j) := by
      let e : F n ≃ {i // r i = J - 1 - (n : ℤ)} :=
        { toFun := fun i => ⟨i, hgen n i⟩
          invFun := fun i => ⟨i, by dsimp [deficit]; rw [i.2]; simp⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have he := e.tsum_eq (fun i => w i)
      change (∑' i : F n, w i) = _ at he
      rw [he]
      convert hrow (J - 1 - (n : ℤ)) using 1
      push_cast
      rfl
    simp_rw [heq n]
    rw [tsum_mul_right]
    calc
      _ ≤ (C * (3 : ℝ) ^ ((J : ℝ) - 1 - n - j)) *
          (3 : ℝ) ^ (γ * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (by norm_num) _)
      _ = D * ρ ^ n * ρ := by
        dsimp only [D, ρ]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        simp only [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 2
        ring
      _ ≤ D * ρ ^ n := mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) (pow_nonneg hρ.1 _)) hρ.2.le
  have hg : Summable (fun n : ℕ => D * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ.1 hρ.2).mul_left D
  have hsumrows : Summable (fun n => ∑' i : F n, f i) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun i => hf0 i)) (fun n => (hrows n).2) hg
  have hsum : Summable f := (summable_partition hf0
    (fun i => ⟨deficit i, rfl, fun _ hn => hn.symm⟩)).2
      ⟨fun n => (hrows n).1, hsumrows⟩
  refine ⟨hsum, ?_⟩
  change (∑' i, f i) ≤ _
  rw [← (hsum.hasSum.tsum_fiberwise deficit).tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, D * ρ ^ n := hsumrows.tsum_le_tsum (fun n => (hrows n).2) hg
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hρ.1 hρ.2]
      dsimp only [D, ρ]
      ring

/-- A countable positive block family admits an actual weighted sum, with the
same scalar order envelope. This uses full block coordinates throughout. -/
theorem bridge_block_tsum_bound {d : ℕ} {ι : Type*}
    (A : ι → BlockMat d) (E : BlockMat d) (w c : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hAs : ∀ i, IsSymmetricBlockMat (A i))
    (hAp : ∀ i, Book.Ch02.BlockPosDef (A i))
    (ho : ∀ i, BlockMatLoewnerLE (A i) (blockScale (c i) E))
    (hc : Summable (fun i => w i * c i)) :
    Summable (fun i => w i • toFullBlockMat (A i)) ∧
      BlockMatLoewnerLE (ofFullBlockMat (∑' i, w i • toFullBlockMat (A i)))
        (blockScale (∑' i, w i * c i) E) := by
  have hF := Source.summable_fullBlock_of_order A E w c hw0 hAs hAp ho hc
  refine ⟨hF, ?_⟩
  intro v
  rw [Source.quadratic_tsum_fullBlock _ hF, Source.quadratic_blockScale]
  have hquad := Source.summable_quadratic_fullBlock _ hF v
  have hb := hc.mul_right ((1 / 2 : ℝ) * blockVecDot v (blockMatVecMul E v))
  rw [← tsum_mul_right]
  apply hquad.tsum_le_tsum _ hb
  intro i
  change (1 / 2 : ℝ) * blockVecDot v (blockMatVecMul (blockScale (w i) (A i)) v) ≤ _
  rw [Source.quadratic_blockScale]
  have h := mul_le_mul_of_nonneg_left (ho i v) (hw0 i)
  rw [Source.quadratic_blockScale] at h
  simpa only [mul_assoc] using h

private theorem bridge_block_integral_scale_bound {d : ℕ}
    {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → BlockMat d} {E : BlockMat d}
    (hEp : Book.Ch02.BlockPosDef E)
    (hA : ∀ α β, Integrable (fun a => blockMatEntry (A a) α β) P)
    {X : CoeffSpace d → ℝ} (hX : Integrable X P) (hEX : ∫ a, X a ∂P ≤ 2)
    (c : ℝ) (hc : 0 ≤ c)
    (ho : ∀ᵐ a ∂P, BlockMatLoewnerLE (A a) (blockScale (c * X a) E)) :
    BlockMatLoewnerLE
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (A a) α β ∂P))
      (blockScale (2 * c) E) := by
  have hG (α β : BlockCoord d) : Integrable (fun a =>
      blockMatEntry (blockScale (c * X a) E) α β) P := by
    simp only [blockMatEntry_blockScale]
    exact (hX.const_mul c).mul_const _
  have hi := Analysis.blockMatLoewnerLE_integral hA hG ho
  have he : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (blockScale (c * X a) E) α β ∂P) =
      blockScale (c * ∫ a, X a ∂P) E := by
    rw [← ofFullBlockMat_toFullBlockMat (blockScale (c * ∫ a, X a ∂P) E)]
    congr 1
    funext α β
    simp only [Matrix.of_apply,
      toFullBlockMat_eq_blockMatEntry, blockMatEntry_blockScale,
      integral_mul_const, integral_const_mul]
  rw [he] at hi
  apply hi.trans (Source.blockScale_le_blockScale_of_pos hEp _)
  simpa only [mul_comm c 2] using mul_le_mul_of_nonneg_left hEX hc

private theorem bridge_source_series {d : ℕ} {ι : Type*} [Countable ι]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (N : ℝ) (hN : 1 ≤ N)
    (A : ι → CoeffSpace d → BlockMat d) (E : BlockMat d)
    (hEs : IsSymmetricBlockMat E) (hEp : Book.Ch02.BlockPosDef E)
    (hAm : ∀ i, HasMeasurableBlock P (A i))
    (hAs : ∀ i a, IsSymmetricBlockMat (A i a))
    (hAp : ∀ i a, Book.Ch02.BlockPosDef (A i a))
    (w b : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hb0 : ∀ i, 0 ≤ b i)
    (hwb : Summable (fun i => w i * b i))
    (X : CoeffSpace d → ℝ) (hX0 : ∀ a, 0 ≤ X a)
    (hX : MemLp X (ENNReal.ofReal N) P) (hEX : ∫ a, X a ∂P ≤ 2)
    (c : ℝ) (hc : 0 ≤ c)
    (ho : ∀ᵐ a ∂P, ∀ i,
      BlockMatLoewnerLE (A i a) (blockScale (c * X a * b i) E)) :
    let M := fun a => ofFullBlockMat (∑' i, w i • toFullBlockMat (A i a))
    SchattenMemLp P N M ∧
      (∀ᵐ a ∂P, Summable (fun i => w i • toFullBlockMat (A i a)) ∧
        BlockMatLoewnerLE (M a) (blockScale (c * X a * (∑' i, w i * b i)) E)) ∧
      BlockMatLoewnerLE
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (M a) α β ∂P))
        (blockScale (2 * c * (∑' i, w i * b i)) E) := by
  intro M
  let F := fun i a => w i • toFullBlockMat (A i a)
  let D := fun i => (w i * b i) * (c * blockTrace E)
  have hTr : 0 ≤ blockTrace E := (Source.fullBlock_posSemidef_of_pos hEs hEp).trace_nonneg
  have hD : Summable D := hwb.mul_right _
  have hD0 (i) : 0 ≤ D i := mul_nonneg (mul_nonneg (hw0 i) (hb0 i)) (mul_nonneg hc hTr)
  have hFm (i) : HasMeasurableBlock P (fun a => ofFullBlockMat (F i a)) := by
    intro α β
    simpa only [F, blockMatEntry_ofFullBlockMat, Matrix.smul_apply, smul_eq_mul,
      toFullBlockMat_eq_blockMatEntry] using (hAm i α β).const_mul (w i)
  have hFs : ∀ᵐ a ∂P, ∀ i, IsSymmetricBlockMat (ofFullBlockMat (F i a)) := by
    apply ae_of_all
    intro a i α β
    simp only [F, blockMatEntry_ofFullBlockMat, Matrix.smul_apply, smul_eq_mul,
      toFullBlockMat_eq_blockMatEntry]
    rw [hAs i a α β]
  have hFn : ∀ᵐ a ∂P, ∀ i, ‖F i a‖ ≤ D i * X a := by
    filter_upwards [ho] with a ha
    intro i
    dsimp only [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
    calc
      _ ≤ w i * (c * X a * b i * blockTrace E) :=
        mul_le_mul_of_nonneg_left (Source.blockOpNorm_le_scale_trace (hAs i a) (hAp i a) (ha i))
          (hw0 i)
      _ = D i * X a := by dsimp only [D]; ring
  have hmem := (Source.lqSchatten_tsum_convergence P N hN F hFm hFs
    D hD0 hD X hX0 hX hFn).1
  have hpath : ∀ᵐ a ∂P, Summable (fun i => F i a) ∧
      BlockMatLoewnerLE (M a) (blockScale (c * X a * (∑' i, w i * b i)) E) := by
    filter_upwards [ho] with a ha
    have he (i) : w i * (c * X a * b i) = c * X a * (w i * b i) := by ring
    have hs : Summable (fun i => w i * (c * X a * b i)) := by
      simp_rw [he]
      exact hwb.mul_left _
    have h := bridge_block_tsum_bound (fun i => A i a) E w (fun i => c * X a * b i)
      hw0 (fun i => hAs i a) (fun i => hAp i a) ha hs
    simp_rw [he, tsum_mul_left] at h
    exact h
  refine ⟨hmem, hpath, ?_⟩
  have hsum0 : 0 ≤ ∑' i, w i * b i := tsum_nonneg (fun i => mul_nonneg (hw0 i) (hb0 i))
  have hp : ∀ᵐ a ∂P, BlockMatLoewnerLE (M a)
      (blockScale ((c * ∑' i, w i * b i) * X a) E) := by
    filter_upwards [hpath] with a ha
    rw [show (c * ∑' i, w i * b i) * X a = c * X a * (∑' i, w i * b i) by ring]
    exact ha.2
  have hi := bridge_block_integral_scale_bound hEp (hmem.integrable_entry hN)
    (hX.integrable (ENNReal.one_le_ofReal.mpr hN)) hEX _ (mul_nonneg hc hsum0) hp
  simpa only [mul_assoc] using hi

/-- The actual fine source tail: one source envelope works simultaneously for
all contained families. The geometric hypotheses are just nonnegative summable
volume weights, the fine row bound, and containment through the parent window. -/
theorem bridge_fine_source_tail (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∃ X : CoeffSpace d → ℝ, (∀ a, 0 ≤ X a) ∧
            MemLp X (ENNReal.ofReal (bigQ d γ : ℝ)) P ∧
            Integrable X P ∧ (∫ a, X a ∂P ≤ 2) ∧
            ∀ (m : Mat d), m.PosDef →
            ∀ (W : Set (Vec d)), W ⊆ centeredCube d (2 * (jStar : ℤ)) →
            ∀ (ι : Type) [Countable ι] (r : ι → ℤ) (y : ι → Vec d) (w : ι → ℝ),
              (∀ i, r i < (jStar : ℤ)) → (∀ i, 0 ≤ w i) → Summable w →
              (∀ i, adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i) ⊆ W) →
              ∀ (j : ℤ) (Cw : ℝ), 0 ≤ Cw →
                (∀ t : ℤ, (∑' i : {i // r i = t}, w i) ≤ Cw * (3 : ℝ) ^ ((t : ℝ) - j)) →
                let M := fun a => ofFullBlockMat (∑' i,
                  w i • toFullBlockMat (coarseBlock
                    (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a))
                SchattenMemLp P (bigQ d γ : ℝ) M ∧
                  (∀ᵐ a ∂P, Summable (fun i => w i • toFullBlockMat (coarseBlock
                    (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a)) ∧
                    BlockMatLoewnerLE (M a)
                      (blockScale (C * Real.sqrt (‖m‖ * ‖m⁻¹‖) * X a * Cw *
                        (3 : ℝ) ^ (-((j : ℝ) - jStar))) E)) ∧
                  BlockMatLoewnerLE
                    (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (M a) α β ∂P))
                    (blockScale (2 * C * Real.sqrt (‖m‖ * ‖m⁻¹‖) * Cw *
                      (3 : ℝ) ^ (-((j : ℝ) - jStar))) E) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, Ca, hCsrc, hCa, hsource⟩ := Source.source_multiplier_and_adapted_bound d hd γ hγ
  let den := 1 - (3 : ℝ) ^ (-(1 - γ))
  have hden : 0 < den := sub_pos.mpr (bridge_fine_ratio_mem_Ico hγ.2).2
  refine ⟨Csrc, Ca / den, hCsrc, div_pos hCa hden, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hjStar hthreshold
  obtain ⟨ell, X, _hell, _hXm, hform, _hgood, hX, _hXi, _hmoment, hnorm, hbound⟩ :=
    hsource P E Ψ K S hstat hdag jStar hjStar hthreshold
  have hX0 (a) : 0 ≤ X a := by rw [hform]; positivity
  have hQ : 1 ≤ (bigQ d γ : ℝ) := by
    exact_mod_cast (Multiscale.bigQ_two_le d γ hγ).trans' (by norm_num)
  have hEX := source_envelope_integral_le_two d hd γ hγ P X hX0 hX hnorm
  refine ⟨X, hX0, hX, hX.integrable (ENNReal.one_le_ofReal.mpr hQ), hEX, ?_⟩
  intro m hm W hW ι hι r y w hr hw0 hw hcell j Cw hCw hrow M
  let A := fun i a => coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) (r i) (y i)) a
  let b := fun i => (3 : ℝ) ^ (γ * ((jStar : ℝ) - r i))
  have hb0 (i) : 0 ≤ b i := Real.rpow_nonneg (by norm_num) _
  have hsum := bridge_fine_weighted_sum w r hw0 hw jStar j hr Cw hCw hrow γ hγ.2
  have hAm (i) : HasMeasurableBlock P (A i) := fun α β =>
    (hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      jStar hjStar m hm (r i) (y i) α β).aestronglyMeasurable
  have ho : ∀ᵐ a ∂P, ∀ i, BlockMatLoewnerLE (A i a)
      (blockScale ((Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * X a * b i) E) := by
    filter_upwards [hbound] with a ha
    intro i
    have hnonneg : 0 ≤ (jStar : ℝ) - r i := by exact_mod_cast (sub_nonneg.mpr (hr i).le)
    simpa only [max_eq_left hnonneg] using ha.2 m hm (r i) (y i) ((hcell i).trans hW)
  have h := bridge_source_series P (bigQ d γ : ℝ) hQ A E
    hdag.refBlock_isSymm hdag.refBlock_posDef hAm
    (fun i a => isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
    (fun i a => blockPosDef_coarseBlock_adapted (explicitRoundedGrid jStar m)
      (isUnit_roundedGrid hjStar hm) (r i) (y i) a)
    w b hw0 hb0 hsum.1 X hX0 hX hEX _ (mul_nonneg hCa.le (Real.sqrt_nonneg _)) ho
  refine ⟨h.1, ?_, ?_⟩
  · filter_upwards [h.2.1] with a ha
    refine ⟨ha.1, ha.2.trans (Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef ?_)⟩
    calc
      _ ≤ (Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖)) * X a *
          (Cw / den * (3 : ℝ) ^ (-((j : ℝ) - jStar))) :=
        mul_le_mul_of_nonneg_left hsum.2
          (mul_nonneg (mul_nonneg hCa.le (Real.sqrt_nonneg _)) (hX0 a))
      _ = _ := by ring
  · apply h.2.2.trans (Source.blockScale_le_blockScale_of_pos hdag.refBlock_posDef _)
    calc
      _ ≤ 2 * (Ca * Real.sqrt (‖m‖ * ‖m⁻¹‖)) *
          (Cw / den * (3 : ℝ) ^ (-((j : ℝ) - jStar))) :=
        mul_le_mul_of_nonneg_left hsum.2 (by positivity)
      _ = _ := by ring

/-- Nonnegative scaling preserves the full quadratic block order. -/
theorem bridge_blockScale_mono {d : ℕ} {A B : BlockMat d} {c : ℝ}
    (hc : 0 ≤ c) (h : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (blockScale c A) (blockScale c B) := by
  intro v
  rw [Source.quadratic_blockScale, Source.quadratic_blockScale]
  exact mul_le_mul_of_nonneg_left (h v) hc

/-- Any source tail bounded by `D E` is converted into a comparison with the
actual old-grid terminal mean. The source constant is selected before the law;
the reference order is derived from the dagger law, never supplied as a premise here. -/
theorem bridge_normalize_source_tail (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ K S →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
          ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
          ∀ m : Mat d, m.PosDef → ∀ s : ℤ, (jStar : ℤ) ≤ s →
            adaptedCell (explicitRoundedGrid jStar m) s ⊆ centeredCube d (2 * (jStar : ℤ)) →
            ∀ (B : BlockMat d) (D : ℝ), 0 ≤ D → BlockMatLoewnerLE B (blockScale D E) →
              BlockMatLoewnerLE B
                (blockScale (D * C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖))
                  (adaptedMean P (explicitRoundedGrid jStar m) s)) := by
  obtain ⟨Csrc, C, hCsrc, hC, hnorm⟩ := adaptedMean_refBlock_normalization d hd γ hγ
  refine ⟨Csrc, C, hCsrc, hC, ?_⟩
  intro P hP E Ψ K S hstat hdag jStar hj hsrc m hm s hs hcell B D hD hB
  have hE := (hnorm P E Ψ K S hstat hdag jStar hj hsrc m hm s hs hcell).2
  have h := hB.trans (bridge_blockScale_mono hD hE)
  have he : blockScale D (blockScale (C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖))
      (adaptedMean P (explicitRoundedGrid jStar m) s)) =
      blockScale (D * C * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖))
        (adaptedMean P (explicitRoundedGrid jStar m) s) := by
    simp only [blockScale, smul_smul, mul_assoc]
  rwa [he] at h

private theorem bridge_source_square_factor {Pi a b : ℝ}
    (hPi : 0 ≤ Pi) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Pi * a ^ 2 ≤ 1 + Pi * (a + b) ^ 2 := by
  have hs : a ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ ha (le_add_of_nonneg_right hb) 2
  linarith only [mul_le_mul_of_nonneg_left hs hPi]

/-- The two old-grid eccentricity factors can be enlarged to the printed
squared sum; the faster source decay can be weakened to the printed exponent.
One factor comes from the source estimate and one from old-grid normalization in the
proof of `p.successful.short.bridge`, near `e.two.grid.source.normalization`. The proof
does not require normalization on the other grid. -/
theorem bridge_source_normalization_factor {Pi a b t γ : ℝ}
    (hPi : 0 ≤ Pi) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hγ : 0 ≤ γ) :
    Pi * a ^ 2 * (3 : ℝ) ^ (-t) ≤
      (1 + Pi * (a + b) ^ 2) * (3 : ℝ) ^ (-(1 - γ) * t) := by
  have hexp : -t ≤ -(1 - γ) * t := by
    have h := mul_nonneg hγ ht
    linarith only [h]
  exact mul_le_mul (bridge_source_square_factor hPi ha hb)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    (Real.rpow_nonneg (by norm_num) _) (by positivity)

end
end HCPolySupport.HighContrast.Annealed
