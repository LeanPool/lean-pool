/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.TransportSetup

/-!
# High-contrast homogenization: Entry.Annealed.TransportReduction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Two-grid transport reduction

This module proves the block arithmetic underlying the two-grid transport estimate
`p.two.grid.transport`. It establishes the scale-monotonicity of the doubled identity and
the trace excess of subtracting that identity, the comparison of normalized blocks at
Schatten order one, and the uniform bound on the normalization loss over the window
`δ ∈ [0, 1/4]`. It then records the deterministic weighted gap inequality and the finite
and centred mean-split identities that decompose a normalized Whitney sum into its row
means plus one integrable tail, the splitting of the actual sum into a bulk row, boundary
rows and the fine subseries, the convexity, scaling and addition estimates for the source
and mean-penalty powers, and the pointwise comparison of a normalized row taken before
any maximum over rows or target cells.
-/
open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean blockScale blockSub
  blockTrace coarseBlock isSymmetricBlockMat_coarseBlockMatrix matSqrt normalizedBlock
  toFullBlockMat_eq_blockMatEntry)
open HCPolySupport.HighContrast (adaptedCell adaptedCellTranslate)
namespace HCPolySupport.HighContrast.Annealed
open MeasureTheory Geometry Multiscale Analysis
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix
noncomputable section

/-- Scalar order on the doubled identity, including zero coefficients. -/
theorem transport_identity_scale_mono {d : ℕ} {x y : ℝ} (hxy : x ≤ y) :
    BlockMatLoewnerLE (blockScale x (Book.Ch02.blockIdentity d)) (blockScale y
      (Book.Ch02.blockIdentity d)) := by
  have hI : (1 : FullBlockMat d).PosSemidef := Matrix.nonneg_iff_posSemidef.mp zero_le_one
  have hs : x • (1 : FullBlockMat d) ≤ y • (1 : FullBlockMat d) := by
    apply Matrix.le_iff.mpr
    rw [← sub_smul]; exact hI.smul (sub_nonneg.mpr hxy)
  have hf : toFullBlockMat (blockScale x (Book.Ch02.blockIdentity d)) ≤
      toFullBlockMat (blockScale y (Book.Ch02.blockIdentity d)) := by
    simpa only [toFullBlockMat_blockScale, toFullBlockMat_blockIdentity] using hs
  simpa only [ofFullBlockMat_toFullBlockMat] using blockMatLoewnerLE_of_le hf
theorem transport_trace_excess {d : ℕ} (A : BlockMat d) :
    blockTrace (blockSub A (Book.Ch02.blockIdentity d)) = blockTrace A - 2 * (d : ℝ) := by
  have hsub : toFullBlockMat (blockSub A (Book.Ch02.blockIdentity d)) = toFullBlockMat A - 1 := by
    ext (i | i) (j | j) <;>
      simp [blockSub, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat,
        Matrix.one_apply]
  rw [blockTrace, hsub, Matrix.trace_sub, Matrix.trace_one]; simp only [BlockCoord,
    Fintype.card_sum, Fintype.card_fin, Nat.cast_add, two_mul, blockTrace]
/-- The additive Cδ error comes from subtracting the doubled identity after the norm change. -/
theorem transport_trace_normalizer_comparison {d : ℕ} {F H X : BlockMat d} (hF : (toFullBlockMat
  F).PosDef) (hH : (toFullBlockMat H).PosDef)
    (hX : (toFullBlockMat X).PosSemidef) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4)) (hlow :
      BlockMatLoewnerLE (blockScale (1 - δ) F) H)
    (hup : BlockMatLoewnerLE H (blockScale (1 + δ) F)) :
    blockTrace (blockSub (normalizedBlock X H) (Book.Ch02.blockIdentity d)) ≤
      (1 - δ)⁻¹ * blockTrace (blockSub (normalizedBlock X F) (Book.Ch02.blockIdentity d)) +
        2 * (d : ℝ) * δ / (1 - δ) := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδ.2 (by norm_num)
  have hn (A : BlockMat d) (hA : (toFullBlockMat A).PosDef) :
      (toFullBlockMat (normalizedBlock X A)).PosSemidef := by
    have hS := matSqrt_inv_posDef_full hA
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      hX.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat A)⁻¹)
  have ht := (transport_schatten_normalizer_comparison hF hH hX.isHermitian (N := 1) le_rfl hδ
    hlow hup).2
  rw [absSchattenNorm_one_eq_blockTrace (hn F hF), absSchattenNorm_one_eq_blockTrace (hn H hH)]
    at ht; rw [transport_trace_excess, transport_trace_excess]
  have he : (1 - δ)⁻¹ * (2 * (d : ℝ)) - 2 * (d : ℝ) = 2 * (d : ℝ) * δ / (1 - δ) := by
    field_simp [(sub_pos.mpr hδ1).ne']
    ring
  nlinarith only [ht, he]
/-- The fixed δ-window makes both normalization losses uniformly bounded. -/
theorem transport_delta_bounds (d : ℕ) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    (1 - δ)⁻¹ ≤ 4 / 3 ∧ 2 * (d : ℝ) * δ / (1 - δ) ≤ (8 / 3) * (d : ℝ) * δ := by
  have hδ0 := hδ.1
  have hpos : 0 < 1 - δ := by linarith only [hδ.2]
  have hi : (1 - δ)⁻¹ ≤ 4 / 3 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith only [hδ.2]
  refine ⟨hi, ?_⟩
  calc
    _ = (2 * (d : ℝ) * δ) * (1 - δ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (2 * (d : ℝ) * δ) * (4 / 3) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring
/-- The deterministic term in the joint gap is a sum of mean penalties.
The centered term remains under the joint maximum. -/
theorem transport_weighted_gap_mean {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure
  P] (Q : ℕ) (hQ : 2 ≤ Q) {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (F G : ι → CoeffSpace d → BlockMat d) (hF : ∀ i ∈ I,
      SchattenMemLp P Q (F i)) (hG : ∀ i ∈ I, SchattenMemLp P Q (G i))
    (hFpos : ∀ i ∈ I, ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F i a)) (hFG : ∀ i ∈ I, ∀ᵐ
      a ∂P, BlockMatLoewnerLE (F i a) (G i a))
    (hmean : ∀ i ∈ I, BlockMatLoewnerLE (Book.Ch02.blockIdentity d)
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P))) :
    let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
    let MG := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G i a) α β ∂P)
    (∫ a, (⨆ i ∈ (I : Set ι), w i * blockOpNorm (blockSub (F i a) (MF i))) ^ (Q : ℝ) ∂P) ≤
      2 ^ ((Q : ℝ) - 1) * (1 + (2 * (d : ℝ)) ^ (Q : ℝ)⁻¹) ^ (Q : ℝ) *
        (∫ a, (⨆ i ∈ (I : Set ι), w i * absSchattenNorm Q (blockSub (G i a) (MG i))) ^ (Q : ℝ) ∂P) +
      2 ^ (2 * (Q : ℝ) - 1) * (1 + (d : ℝ) ^ (1 - (Q : ℝ)⁻¹)) ^ (Q : ℝ) *
        ∑ i ∈ I, w i ^ (Q : ℝ) * meanPenalty Q (MG i) := by
  intro MF MG
  have hQ1 : 1 ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ2 : 2 ≤ (Q : ℝ) := by exact_mod_cast hQ
  apply (positiveGap_weighted_joint_max_pow d hQ2 I hI w hw F G hF hG hFpos hFG).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  have hFs : IsSymmetricBlockMat (MF i) := isSymmetricBlockMat_integral (hF i hi).symmetric
  have hGs : IsSymmetricBlockMat (MG i) := isSymmetricBlockMat_integral (hG i hi).symmetric
  have horder : BlockMatLoewnerLE (MF i) (MG i) := blockMatLoewnerLE_integral ((hF i
    hi).integrable_entry hQ1) ((hG i hi).integrable_entry hQ1) (hFG i hi)
  have hp := (meanPenalty_mono_and_dominates Q (by omega) hFs hGs (hmean i hi) horder).2
  have ht : blockTrace (blockSub (MG i) (MF i)) ≤
      blockTrace (blockSub (MG i) (Book.Ch02.blockIdentity d)) := by
    have htr := blockTrace_identity_sub_nonneg (MF i) hFs (hmean i hi)
    have he (A B : BlockMat d) : blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
      have hab : toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
        ext (a | a) (b | b) <;> rfl
      exact (congrArg Matrix.trace hab).trans (Matrix.trace_sub _ _)
    rw [he] at htr; rw [he, he]; linarith only [htr]
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left ht
    (Real.rpow_nonneg (norm_nonneg _) _)).trans hp) (Real.rpow_nonneg (hw i) _)
private theorem transport_full_sub {d : ℕ} (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext (i | i) (j | j) <;> rfl
/-- Expectation respects an a.e. finite decomposition with one integrable tail. -/
theorem transport_mean_finite_split {d : ℕ} {P : Measure (CoeffSpace d)} [IsFiniteMeasure P]
    {N : ℝ} (hN : 1 ≤ N) {ι : Type*} (s : Finset ι)
    (F : ι → CoeffSpace d → BlockMat d) (G T : CoeffSpace d → BlockMat d) (hF : ∀ i ∈ s,
      SchattenMemLp P N (F i)) (hT : SchattenMemLp P N T)
    (hsplit : ∀ᵐ a ∂P, toFullBlockMat (G a) = (∑ i ∈ s, toFullBlockMat (F i a)) + toFullBlockMat
      (T a)) :
    let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
    let MG := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    let MT := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (T a) α β ∂P)
    toFullBlockMat MG = (∑ i ∈ s, toFullBlockMat (MF i)) + toFullBlockMat MT := by
  intro MF MG MT
  ext α β; simp only [MG, MF, MT, toFullBlockMat_ofFullBlockMat, Matrix.of_apply,
    Matrix.sum_apply, Matrix.add_apply]
  calc
    _ = ∫ a, (∑ i ∈ s, blockMatEntry (F i a) α β) + blockMatEntry (T a) α β ∂P := by
      apply integral_congr_ae
      filter_upwards [hsplit] with a ha
      simpa only [Matrix.sum_apply, Matrix.add_apply, toFullBlockMat_eq_blockMatEntry] using
        congrArg (fun A : FullBlockMat d => A α β) ha
    _ = _ := by
      rw [integral_add (integrable_finsetSum _ (fun i hi => (hF i hi).integrable_entry hN α β))
        (hT.integrable_entry hN α β), integral_finsetSum _ (fun i hi => (hF i
          hi).integrable_entry hN α β)]
/-- Centering commutes with a finite row decomposition plus one integrable tail.
The triangle estimate has no factor for the number of rows. -/
theorem transport_centered_finite_split {d : ℕ} {P : Measure (CoeffSpace d)}
  [IsProbabilityMeasure P]
    {N : ℝ} (hN : 1 ≤ N) {ι : Type*} (s : Finset ι)
    (F : ι → CoeffSpace d → BlockMat d) (G T : CoeffSpace d → BlockMat d) (hF : ∀ i ∈ s,
      SchattenMemLp P N (F i)) (hG : SchattenMemLp P N G) (hT : SchattenMemLp P N T)
    (hsplit : ∀ᵐ a ∂P, toFullBlockMat (G a) = (∑ i ∈ s, toFullBlockMat (F i a)) + toFullBlockMat
      (T a)) :
    let MF := fun i => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F i a) α β ∂P)
    let MG := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    let MT := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (T a) α β ∂P)
    ∀ᵐ a ∂P, absSchattenNorm N (blockSub (G a) MG) ≤ (2 * (d : ℝ)) ^ N⁻¹ *
      ((∑ i ∈ s, absSchattenNorm N (blockSub (F i a) (MF i))) + absSchattenNorm N (blockSub (T
        a) MT)) := by
  intro MF MG MT
  have hmean : toFullBlockMat MG = (∑ i ∈ s, toFullBlockMat (MF i)) + toFullBlockMat MT :=
    transport_mean_finite_split hN s F G T hF hT hsplit
  filter_upwards [hsplit, (hG.center hN).symmetric, (hT.center hN).symmetric,
    (Filter.eventually_all_finset s).mpr (fun i hi => ((hF i hi).center hN).symmetric)] with a
      ha hGa hTa hFa
  have he : toFullBlockMat (blockSub (G a) MG) =
      (∑ i ∈ s, toFullBlockMat (blockSub (F i a) (MF i))) + toFullBlockMat (blockSub (T a) MT) := by
    simp only [transport_full_sub, ha, hmean, Finset.sum_sub_distrib]
    abel
  apply (absSchattenNorm_le_dim_rpow_mul_blockOpNorm ((toFullBlockMat_isHermitian_iff _).mpr
    hGa) hN).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [blockOpNorm, he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun i hi => blockOpNorm_le_absSchattenNorm
      ((toFullBlockMat_isHermitian_iff _).mpr (hFa i hi)) hN
  · exact blockOpNorm_le_absSchattenNorm ((toFullBlockMat_isHermitian_iff _).mpr hTa) hN
/-- A positive tail bounded by one scalar envelope stays bounded after centering.
The same X is available to the later joint maximum. -/
theorem transport_centered_tail_envelope {d : ℕ} {P : Measure (CoeffSpace d)}
  [IsProbabilityMeasure P]
    {N : ℝ} (hN : 1 ≤ N) (T : CoeffSpace d → BlockMat d) (hT : SchattenMemLp P N T)
    (X : CoeffSpace d → ℝ) (hX : Integrable X P) (hEX : ∫ a, X a ∂P ≤ 2) (c : ℝ) (hc : 0 ≤ c)
      (hpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (T a))
    (hbound : ∀ᵐ a ∂P, BlockMatLoewnerLE (T a) (blockScale (c * X a) (Book.Ch02.blockIdentity d))) :
    let MT := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (T a) α β ∂P)
    blockTrace MT ≤ 2 * (d : ℝ) * c * 2 ∧
      ∀ᵐ a ∂P, absSchattenNorm N (blockSub (T a) MT) ≤ 2 * (d : ℝ) * c * (X a + 2) := by
  intro MT
  have hdata := positiveGap_ordered_data hN hT hT hpos (Filter.Eventually.of_forall (fun _ _ =>
    le_rfl))
  have hMT : (toFullBlockMat MT).PosSemidef := hdata.2.2.2.1
  have htr (b : ℝ) : blockTrace (blockScale b (Book.Ch02.blockIdentity d)) = 2 * (d : ℝ) * b := by
    have hi : toFullBlockMat (blockScale b (Book.Ch02.blockIdentity d)) = b • 1 := by
      ext (i | i) (j | j) <;>
        simp [blockScale, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat,
          Matrix.one_apply]
    rw [blockTrace, hi, Matrix.trace_smul, Matrix.trace_one]; simp only [BlockCoord,
      Fintype.card_sum, Fintype.card_fin, Nat.cast_add, smul_eq_mul]; ring
  have htrace : ∀ᵐ a ∂P, blockTrace (T a) ≤ 2 * (d : ℝ) * c * X a := by
    filter_upwards [hbound] with a ha
    exact (Source.blockTrace_le_of_order ha).trans_eq (by rw [htr]; ring)
  have hmean : blockTrace MT ≤ 2 * (d : ℝ) * c * 2 := by
    have ht := blockTrace_integral (hT.integrable_entry hN)
    calc
      _ = ∫ a, blockTrace (T a) ∂P := ht.2
      _ ≤ ∫ a, 2 * (d : ℝ) * c * X a ∂P := integral_mono_ae ht.1 (hX.const_mul _) htrace
      _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hEX (by positivity)
  refine ⟨hmean, ?_⟩
  filter_upwards [hT.symmetric, hpos, htrace] with a hs hp ht
  have hz : IsSymmetricBlockMat (ofFullBlockMat (0 : FullBlockMat d)) := by intro α β; simp
  have hpsd := (ordered_gap_posSemidef hz hs (fun _ => le_rfl) hp).1
  have hpT : (toFullBlockMat (T a)).PosSemidef := by
    simpa only [transport_full_sub, toFullBlockMat_ofFullBlockMat, sub_zero] using hpsd
  calc
    _ ≤ absSchattenNorm N (T a) + absSchattenNorm N MT := absSchattenNorm_sub_le hpT.isHermitian
      hMT.isHermitian hN
    _ ≤ blockTrace (T a) + blockTrace MT := add_le_add (absSchattenNorm_le_blockTrace hpT hN)
      (absSchattenNorm_le_blockTrace hMT hN)
    _ ≤ _ := by linarith only [ht, hmean]
/-- Stationarity identifies each centered cell in an actual finite Whitney row.
The identity is pointwise and therefore remains valid under the joint maximum. -/
theorem transport_centered_lattice_row (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (j : ℤ) (hj : (jStar :
      ℤ) ≤ j) (Z : Finset (Vec d))
    (hZ : ∀ z ∈ Z, z ∈ adaptedLatticeAtScale (explicitRoundedGrid jStar m) j) (w : Vec d → ℝ) (R
      : BlockMat d) :
    let q := explicitRoundedGrid jStar m
    let A := fun a => normalizedBlock (ofFullBlockMat (∑ z ∈ Z,
      w z • toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))) R
    let MA := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (A a) α β ∂P)
    MA = blockScale (∑ z ∈ Z, w z) (normalizedBlock (adaptedMean P q j) R) ∧
      ∀ a, blockSub (A a) MA = ofFullBlockMat (∑ z ∈ Z, w z • toFullBlockMat
        (normalizedBlock (blockSub (coarseBlock (adaptedCellTranslate q j z) a) (adaptedMean P q
          j)) R)) := by
  let : NeZero d := ⟨by omega⟩
  intro q A MA
  have hmem (z : Vec d) := Source.memLqSchatten_normalizedBlock
    (Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j z
    1 le_rfl)
    le_rfl R
  have hE (z : Vec d) (hz : z ∈ Z) : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (normalizedBlock (coarseBlock (adaptedCellTranslate q j z) a) R) α β ∂P) =
      normalizedBlock (adaptedMean P q j) R := by
    have hc := Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      jStar hjStar m hm j z 1 le_rfl
    exact (integral_normalizedBlock_coarseBlock (hc.integrable_entry le_rfl) R).trans
      (congrArg (fun B => normalizedBlock B R)
        (by
          rcases hZ z hz with ⟨v, hv⟩
          rw [← hv]
          exact annealedBlock_adaptedCellTranslate_lattice P hstat jStar hjStar m hm hj v))
  have hlin (a : CoeffSpace d) : toFullBlockMat (A a) =
      ∑ z ∈ Z, w z • toFullBlockMat (normalizedBlock (coarseBlock (adaptedCellTranslate q j z)
        a) R) := by
    simp only [A, normalizedBlock, toFullBlockMat_ofFullBlockMat,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hmean : toFullBlockMat MA = (∑ z ∈ Z, w z) • toFullBlockMat (normalizedBlock (adaptedMean
    P q j) R) := by
    ext α β; simp only [MA, toFullBlockMat_ofFullBlockMat, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    calc
      _ = ∫ a, ∑ z ∈ Z, w z * blockMatEntry (normalizedBlock (coarseBlock (adaptedCellTranslate
        q j z) a) R) α β ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a => by
          simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
            toFullBlockMat_eq_blockMatEntry] using
            congrArg (fun B : FullBlockMat d => B α β) (hlin a)
      _ = ∑ z ∈ Z, w z * blockMatEntry (normalizedBlock (adaptedMean P q j) R) α β := by
        rw [integral_finsetSum _ (fun z _ => ((hmem z).integrable_entry le_rfl α β).const_mul (w
          z))]
        apply Finset.sum_congr rfl
        intro z hz; rw [integral_const_mul]
        congr 1
        simpa only [blockMatEntry_ofFullBlockMat, Matrix.of_apply] using
          congrArg (fun B : BlockMat d => blockMatEntry B α β) (hE z hz)
      _ = _ := by rw [Finset.sum_mul]; rfl
  constructor
  · rw [← ofFullBlockMat_toFullBlockMat MA, hmean,
      ← ofFullBlockMat_toFullBlockMat (blockScale (∑ z ∈ Z, w z) (normalizedBlock (adaptedMean P
        q j) R))]
    congr 1
    ext (i | i) (j | j) <;> rfl
  · intro a
    rw [← ofFullBlockMat_toFullBlockMat (blockSub (A a) MA)]
    congr 1
    simp only [transport_full_sub, hlin, hmean, normalizedBlock, toFullBlockMat_ofFullBlockMat,
      Matrix.mul_sub, Matrix.sub_mul, smul_sub, Finset.sum_sub_distrib]
    congr 1; rw [Finset.sum_smul]
/-- At the trace level, missing volume is filled by the identity. The finite
part has mass at most one, so the normalization error is Cδ, independent of
how many rows or cells occur. -/
theorem transport_mean_trace_split {d : ℕ} {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (A : ι →
  BlockMat d) (F H G T : BlockMat d) (hF : (toFullBlockMat F).PosDef) (hH : (toFullBlockMat
  H).PosDef)
    {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hlow : BlockMatLoewnerLE (blockScale (1 - δ) F) H) (hup : BlockMatLoewnerLE H (blockScale
      (1 + δ) F)) (hlam : ∀ i ∈ s, 0 ≤ lam i) (hmass : ∑ i ∈ s, lam i ≤ 1)
    (hA : ∀ i ∈ s, (toFullBlockMat (A i)).PosSemidef) (ht : ∀ i ∈ s, 0 ≤ blockTrace (blockSub
      (normalizedBlock (A i) F) (Book.Ch02.blockIdentity d)))
    (hsplit : toFullBlockMat G = (∑ i ∈ s, lam i • toFullBlockMat (normalizedBlock (A i) H)) +
      toFullBlockMat T)
    (u : ℝ) (hT : blockTrace T ≤ u) :
    blockTrace (blockSub G (Book.Ch02.blockIdentity d)) ≤
      (4 / 3 : ℝ) * (∑ i ∈ s, lam i * blockTrace (blockSub (normalizedBlock (A i) F)
        (Book.Ch02.blockIdentity d))) +
        (8 / 3 : ℝ) * (d : ℝ) * δ + u := by
  have hb := transport_delta_bounds d hδ
  have hrow (i) (hi : i ∈ s) : blockTrace (blockSub (normalizedBlock (A i) H)
    (Book.Ch02.blockIdentity d)) ≤
      (4 / 3 : ℝ) * blockTrace (blockSub (normalizedBlock (A i) F) (Book.Ch02.blockIdentity d)) +
        (8 / 3 : ℝ) * (d : ℝ) * δ :=
    (transport_trace_normalizer_comparison hF hH (hA i hi) hδ hlow hup).trans (add_le_add
      (mul_le_mul_of_nonneg_right hb.1 (ht i hi)) hb.2)
  have hsum := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (hlam i hi))
  have he : (∑ i ∈ s, lam i * ((4 / 3 : ℝ) *
      blockTrace (blockSub (normalizedBlock (A i) F) (Book.Ch02.blockIdentity d)) + (8 / 3 : ℝ)
        * d * δ)) =
      (4 / 3 : ℝ) * (∑ i ∈ s, lam i * blockTrace (blockSub (normalizedBlock (A i) F)
        (Book.Ch02.blockIdentity d))) +
        ((8 / 3 : ℝ) * d * δ) * ∑ i ∈ s, lam i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi; ring
  rw [he] at hsum
  have htr : blockTrace G = (∑ i ∈ s, lam i * blockTrace (normalizedBlock (A i) H)) + blockTrace
    T := by
    simp only [blockTrace, hsplit, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
  have hid : blockTrace (blockSub G (Book.Ch02.blockIdentity d)) =
      (∑ i ∈ s, lam i * blockTrace (blockSub (normalizedBlock (A i) H) (Book.Ch02.blockIdentity
        d))) +
        2 * (d : ℝ) * ((∑ i ∈ s, lam i) - 1) + blockTrace T := by
    simp only [transport_trace_excess, htr, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  have herr : ((8 / 3 : ℝ) * d * δ) * (∑ i ∈ s, lam i) ≤ (8 / 3 : ℝ) * d * δ := by
    have hd0 : 0 ≤ (8 / 3 : ℝ) * d * δ := mul_nonneg (by positivity) hδ.1
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass hd0
  have hmissing : 2 * (d : ℝ) * ((∑ i ∈ s, lam i) - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by
    positivity) (sub_nonpos.mpr hmass)
  rw [hid]; linarith only [hsum, herr, hmissing, hT]
/-- The actual normalized Whitney sum has precisely a finite bulk row, finite
boundary rows, and the fine subseries. Convergence is supplied by the source
bounds; no coarse block is evaluated on the remainder of the partition. -/
theorem transport_whitney_raw_split {d : ℕ} (q : Mat d) (hq : IsUnit q) (W : Set (Vec d)) (J cap
  : ℤ) (hJ : J ≤ cap) (hfin : ∀ t ≤ cap, (maximalAdaptedCellCenters W q cap t).Finite)
    (a : CoeffSpace d) (R : BlockMat d) :
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    let f := fun p : I => ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume
      W).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a)
    let Z := fun t => if ht : t ≤ cap then (hfin t ht).toFinset else ∅
    let row := fun t => ofFullBlockMat (∑ z ∈ Z t,
      ((volume (adaptedCell q t)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellTranslate q t z) a))
    let fine := ofFullBlockMat (∑' p : {p : I // p.1.1 < J}, f p)
    Summable f →
      toFullBlockMat (normalizedBlock (ofFullBlockMat (∑' p, f p)) R) =
        toFullBlockMat (normalizedBlock (row cap) R) +
        (∑ t ∈ Finset.Icc J (cap - 1), toFullBlockMat (normalizedBlock (row t) R)) +
        toFullBlockMat (normalizedBlock fine R) := by
  intro I f Z row fine hsum
  have hvol (t : ℤ) (v : Fin d → ℤ) : volume (adaptedCellAtCenter q t v) = volume (adaptedCell q
    t) := by
    rw [volume_adaptedCellAtCenter, ← adaptedCellTranslate_zero q t, volume_adaptedCellTranslate]
  have hrow (t : ℤ) (ht : t ≤ cap) : (∑' p : {p : I // p.1.1 = t}, f p) = toFullBlockMat (row t)
    := by
    have hz : Z t = (hfin t ht).toFinset := dite_eq_left ht
    simp only [row, hz, toFullBlockMat_ofFullBlockMat]
    rw [← transport_maximal_row_reindex W q hq cap t (hfin t ht)
      (fun z => ((volume (adaptedCell q t)).toReal / (volume W).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellTranslate q t z) a))]
    apply tsum_congr
    intro p
    dsimp only [f, adaptedCellAtCenter]
    have hp := p.2
    change p.1.1.1 = t at hp
    rw [hp]
    rw [show volume (adaptedCellTranslate q t (adaptedCellCenter q t p.1.1.2)) =
      volume (adaptedCell q t) from hvol t p.1.1.2]
  have hthree := transport_series_three_parts f hsum (fun p : I => p.1.1) J cap hJ (fun p =>
    p.2.1.1)
  have hraw : (∑' p, f p) = toFullBlockMat (row cap) +
      (∑ t ∈ Finset.Icc J (cap - 1), toFullBlockMat (row t)) + toFullBlockMat fine := by
    rw [hthree, hrow cap le_rfl]; simp only [fine, toFullBlockMat_ofFullBlockMat]
    congr 2
    exact Finset.sum_congr rfl fun t ht => hrow t (by have := (Finset.mem_Icc.mp ht).2; omega)
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hraw,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul]
/-- The normalizer change is pointwise on the whole centered row, before any
maximum over rows or target cells is taken. -/
theorem transport_row_normalizer_comparison {d : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ) (X :
  ι → BlockMat d) (hX : ∀ i ∈ s, (toFullBlockMat (X i)).IsHermitian)
    {F H : BlockMat d} (hF : (toFullBlockMat F).PosDef) (hH : (toFullBlockMat H).PosDef)
    {N : ℝ} (hN : 1 ≤ N) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4))
    (hlow : BlockMatLoewnerLE (blockScale (1 - δ) F) H)
    (hup : BlockMatLoewnerLE H (blockScale (1 + δ) F)) :
    absSchattenNorm N (ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat (normalizedBlock (X i) H))) ≤
      (4 / 3 : ℝ) * absSchattenNorm N (ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat
        (normalizedBlock (X i) F))) := by
  let B := ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat (X i))
  have hB : (toFullBlockMat B).IsHermitian := by
    apply (toFullBlockMat_isHermitian_iff _).mpr
    intro α β
    simp only [B, blockMatEntry_ofFullBlockMat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      toFullBlockMat_eq_blockMatEntry]
    exact Finset.sum_congr rfl fun i hi => congrArg (fun x : ℝ => w i * x)
      ((toFullBlockMat_isHermitian_iff _).mp (hX i hi) α β)
  have hlin (R : BlockMat d) : normalizedBlock B R =
      ofFullBlockMat (∑ i ∈ s, w i • toFullBlockMat (normalizedBlock (X i) R)) := by
    simp only [B, normalizedBlock, toFullBlockMat_ofFullBlockMat,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [← hlin H, ← hlin F]
  have hS := matSqrt_inv_posDef_full hF
  have hBF : (toFullBlockMat (normalizedBlock B F)).IsHermitian := by
    simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hS.isHermitian.eq] using
      Matrix.isHermitian_conjTranspose_mul_mul (matSqrt (toFullBlockMat F)⁻¹) hB
  exact (transport_schatten_normalizer_comparison hF hH hB hN hδ hlow hup).2.trans
    (mul_le_mul_of_nonneg_right (transport_delta_bounds d hδ).1 (absSchattenNorm_nonneg hBF hN))
/-- `p.two.grid.transport`,
with the actual Whitney rows. The hypotheses on the fine
part are the normalized conclusions of `transport_fine_source_tail`; the
membership of the whole sum is furnished by `exists_transport_whitney_ordered_data`.
One scalar X controls the tail for every subsequent target. -/
theorem transport_centered_whitney_bound (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m mPlus : Mat d) (hm : m.PosDef) (hmPlus :
      mPlus.PosDef) (oldEnd newEnd cap : ℤ) (hcap : (jStar : ℤ) ≤ cap) (W : Set (Vec d))
    (hfin : ∀ t ≤ cap, (maximalAdaptedCellCenters W (explicitRoundedGrid jStar m) cap t).Finite)
      (N : ℝ) (hN : 1 ≤ N) (X : CoeffSpace d → ℝ) (hX : Integrable X P) (hEX : ∫ a, X a ∂P ≤ 2)
    (c : ℝ) (hc : 0 ≤ c) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 4)) :
    let q := explicitRoundedGrid jStar m
    let F := adaptedMean P q oldEnd
    let H := adaptedMean P (explicitRoundedGrid jStar mPlus) newEnd
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    let f := fun (p : I) a => ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume
      W).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a)
    let Z := fun t => if ht : t ≤ cap then (hfin t ht).toFinset else ∅
    let G := fun a => normalizedBlock (ofFullBlockMat (∑' p, f p a)) H
    let T := fun a => normalizedBlock (ofFullBlockMat (∑' p : {p : I // p.1.1 < (jStar : ℤ)}, f
      p a)) H
    let V := fun t a => ofFullBlockMat (∑ z ∈ Z t, ((volume (adaptedCell q t)).toReal / (volume
      W).toReal) •
      toFullBlockMat (normalizedBlock (blockSub (coarseBlock (adaptedCellTranslate q t z) a)
        (adaptedMean P q t)) F))
    BlockMatLoewnerLE (blockScale (1 - δ) F) H → BlockMatLoewnerLE H (blockScale (1 + δ) F) →
    SchattenMemLp P N G → SchattenMemLp P N T → (∀ᵐ a ∂P, Summable (fun p => f p a)) →
    (∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (T a)) →
    (∀ᵐ a ∂P, BlockMatLoewnerLE (T a) (blockScale (c * X a) (Book.Ch02.blockIdentity d))) →
    let MG := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)
    ∀ᵐ a ∂P, absSchattenNorm N (blockSub (G a) MG) ≤
      ((4 / 3 : ℝ) * (2 * (d : ℝ)) ^ N⁻¹) *
        (absSchattenNorm N (V cap a) + ∑ t ∈ Finset.Icc (jStar : ℤ) (cap - 1), absSchattenNorm N
          (V t a)) +
      ((2 * (d : ℝ)) ^ N⁻¹ * (2 * (d : ℝ)) * c) * (X a + 2) := by
  let : NeZero d := ⟨by omega⟩
  intro q F H I f Z G T V hlow hup hG hT hseries hTpos hTbound MG
  have hq := isUnit_roundedGrid hjStar hm
  have hF := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm oldEnd
  have hH := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar mPlus hmPlus newEnd
  let row := fun t a => normalizedBlock (ofFullBlockMat (∑ z ∈ Z t,
    ((volume (adaptedCell q t)).toReal / (volume W).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellTranslate q t z) a))) H
  let mr := fun t => ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (row t a) α β ∂P)
  let mt := ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (T a) α β ∂P)
  let J := Finset.Icc (jStar : ℤ) cap
  have hcapJ : cap ∈ J := Finset.mem_Icc.mpr ⟨hcap, le_rfl⟩
  have herase : J.erase cap = Finset.Icc (jStar : ℤ) (cap - 1) := by
    ext t; simp only [J, Finset.mem_erase, Finset.mem_Icc]; omega
  have hsplit (A : ℤ → FullBlockMat d) : (∑ t ∈ J, A t) = A cap + ∑ t ∈ Finset.Icc (jStar : ℤ)
    (cap - 1), A t := by
    rw [← Finset.sum_erase_add _ _ hcapJ, herase, add_comm]
  have hrowMem (t : ℤ) : SchattenMemLp P N (row t) := Source.memLqSchatten_normalizedBlock
    (Source.memLqSchatten_finset_sum hN (Z t) (fun _ => (volume (adaptedCell q t)).toReal /
      (volume W).toReal)
      (fun z a => coarseBlock (adaptedCellTranslate q t z) a)
      (fun z _ => Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hjStar m hm t z N hN)) hN H
  have hdecomp : ∀ᵐ a ∂P, toFullBlockMat (G a) = (∑ t ∈ J, toFullBlockMat (row t a)) +
    toFullBlockMat (T a) := by
    filter_upwards [hseries] with a ha
    rw [hsplit]; exact transport_whitney_raw_split q hq W jStar cap hcap hfin a H ha
  have hcenter := transport_centered_finite_split hN J row G T (fun t _ => hrowMem t) hG hT hdecomp
  have htail := transport_centered_tail_envelope hN T hT X hX hEX c hc hTpos hTbound
  have hrow (t : ℤ) (ht : t ∈ J) (a : CoeffSpace d) :
      absSchattenNorm N (blockSub (row t a) (mr t)) ≤ (4 / 3 : ℝ) * absSchattenNorm N (V t a) := by
    have htl := (Finset.mem_Icc.mp ht).1
    have htu := (Finset.mem_Icc.mp ht).2
    have hZ (z) (hz : z ∈ Z t) : z ∈ adaptedLatticeAtScale q t := by
      have hz' : z ∈ maximalAdaptedCellCenters W q cap t := (hfin t htu).mem_toFinset.mp (by
        simpa only [Z, dite_eq_left htu] using hz)
      rcases hz' with ⟨v, _hv, rfl⟩
      exact ⟨v, rfl⟩
    have he := (transport_centered_lattice_row d hd P γ E Ψ K S hstat hdag jStar hjStar m hm
      t htl (Z t) hZ (fun _ => (volume (adaptedCell q t)).toReal / (volume W).toReal) H).2 a
    change absSchattenNorm N (blockSub (row t a) (mr t)) ≤ _
    rw [he]
    apply transport_row_normalizer_comparison (Z t)
      (fun _ => (volume (adaptedCell q t)).toReal / (volume W).toReal) _ _ hF hH hN hδ hlow hup
    intro z hz; rw [transport_full_sub]
    exact ((toFullBlockMat_isHermitian_iff _).mpr (isSymmetricBlockMat_coarseBlockMatrix
      (adaptedCellTranslate q t z) (⇑a.1))).sub
      (adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm t).isHermitian
  have hsplitR (A : ℤ → ℝ) : (∑ t ∈ J, A t) = A cap + ∑ t ∈ Finset.Icc (jStar : ℤ) (cap - 1), A
    t := by
    rw [← Finset.sum_erase_add _ _ hcapJ, herase, add_comm]
  filter_upwards [hcenter, htail.2] with a ha hta
  have hr := Finset.sum_le_sum (fun t ht => hrow t ht a)
  rw [← Finset.mul_sum] at hr
  conv at hr => rhs; rw [hsplitR]
  calc
    _ ≤ _ := ha
    _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * ((4 / 3 : ℝ) *
        (absSchattenNorm N (V cap a) + ∑ t ∈ Finset.Icc (jStar : ℤ) (cap - 1), absSchattenNorm N
          (V t a)) +
        2 * (d : ℝ) * c * (X a + 2)) := mul_le_mul_of_nonneg_left (add_le_add hr hta) (by
          positivity)
    _ = _ := by ring
/-- Insert the missing mass at trace excess zero before applying convexity. -/
theorem meanPenalty_convex_combination (Q : ℕ) {ι : Type*} (s : Finset ι) (lam t : ι → ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (ht : ∀ i ∈ s, 0 ≤ t i) (hsum : ∑ i ∈ s, lam i ≤ 1) :
    (1 + ∑ i ∈ s, lam i * t i) ^ Q - 1 ≤ ∑ i ∈ s, lam i * ((1 + t i) ^ Q - 1) := by
  have hh := (convexOn_pow (𝕜 := ℝ) Q).map_add_sum_le (w := lam)
    (p := fun i => 1 + t i) (v := 1 - ∑ i ∈ s, lam i) (q := 1) hlam
    (by ring) (fun i hi => by exact add_nonneg (by norm_num) (ht i hi))
    (sub_nonneg.mpr hsum) (by norm_num)
  simp only [smul_eq_mul, one_pow, mul_one] at hh
  have he : 1 - ∑ i ∈ s, lam i + ∑ i ∈ s, lam i * (1 + t i) =
      1 + ∑ i ∈ s, lam i * t i := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
    ring
  rw [he] at hh; simp only [mul_sub, mul_one, Finset.sum_sub_distrib]; linarith only [hh]
/-- Scaling a nonnegative trace excess costs at most the Q-th power. -/
theorem transport_penalty_scale (Q : ℕ) {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) :
    (1 + c * x) ^ Q - 1 ≤ c ^ Q * ((1 + x) ^ Q - 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    have hc0 := zero_le_one.trans hc
    have hfx : 0 ≤ (1 + x) ^ Q - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith only [hx]))
    have hfcx : 0 ≤ (1 + c * x) ^ Q - 1 := sub_nonneg.mpr (one_le_pow₀ (le_add_of_nonneg_right
      (mul_nonneg hc0 hx)))
    have hcoef : 1 + c * x ≤ c * (1 + x) := by nlinarith only [hc]
    have hlast : c * x ≤ c ^ (Q + 1) * x := by
      rw [pow_succ]
      apply mul_le_mul_of_nonneg_right _ hx
      nlinarith only [mul_le_mul_of_nonneg_right (one_le_pow₀ hc : 1 ≤ c ^ Q) hc0]
    calc
      _ = (1 + c * x) * ((1 + c * x) ^ Q - 1) + c * x := by rw [pow_succ]; ring
      _ ≤ (c * (1 + x)) * (c ^ Q * ((1 + x) ^ Q - 1)) + c ^ (Q + 1) * x := add_le_add
        (mul_le_mul hcoef ih hfcx (by positivity)) hlast
      _ = _ := by rw [pow_succ, pow_succ]; ring
/-- The nonlinear source error retains its first and Q-th powers. -/
theorem transport_penalty_linear_and_power (Q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ Q - 1 ≤ (2 : ℝ) ^ Q * (x + x ^ Q) := by
  by_cases hsmall : x ≤ 1
  · have h := meanPenalty_convex_combination Q {()} (fun _ => x) (fun _ => (1 : ℝ))
      (fun _ _ => hx) (fun _ _ => zero_le_one) (by simpa using hsmall)
    simp only [Finset.sum_singleton, mul_one] at h
    calc
      _ ≤ x * ((2 : ℝ) ^ Q - 1) := by simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using h
      _ ≤ (2 : ℝ) ^ Q * (x + x ^ Q) := by
        have hpow : 0 ≤ (2 : ℝ) ^ Q * x ^ Q := mul_nonneg (by positivity) (pow_nonneg hx Q)
        nlinarith only [hpow, hx]
  · have hlarge : 1 ≤ x := le_of_not_ge hsmall
    calc
      _ ≤ (2 * x) ^ Q := by
        have hh := pow_le_pow_left₀ (by linarith only [hlarge] : 0 ≤ 1 + x) (by linarith only
          [hlarge] : 1 + x ≤ 2 * x) Q
        linarith only [hh]
      _ ≤ _ := by rw [mul_pow]; nlinarith only [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ Q) hx]
/-- Splitting a trace excess costs only a constant depending on Q. -/
theorem transport_penalty_add (Q : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 + (x + y)) ^ Q - 1 ≤ (2 : ℝ) ^ Q * (((1 + x) ^ Q - 1) + ((1 + y) ^ Q - 1)) := by
  have h := meanPenalty_convex_combination Q Finset.univ (fun _ : Bool => (1 / 2 : ℝ))
    (fun i => if i then 2 * x else 2 * y) (by intro i hi; norm_num)
    (by intro i hi; cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity) (by
      norm_num [Fintype.sum_bool])
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at h
  have hh : (1 + (x + y)) ^ Q - 1 ≤
      (1 / 2 : ℝ) * ((1 + 2 * x) ^ Q - 1) + (1 / 2 : ℝ) * ((1 + 2 * y) ^ Q - 1) := by
    convert h using 1
    ring
  have hx' := transport_penalty_scale Q hx (by norm_num : (1 : ℝ) ≤ 2)
  have hy' := transport_penalty_scale Q hy (by norm_num : (1 : ℝ) ≤ 2)
  have hsum : 0 ≤ (2 : ℝ) ^ Q * (((1 + x) ^ Q - 1) + ((1 + y) ^ Q - 1)) := by
    apply mul_nonneg (by positivity)
    exact add_nonneg (sub_nonneg.mpr (one_le_pow₀ (by linarith only [hx]))) (sub_nonneg.mpr
      (one_le_pow₀ (by linarith only [hy])))
  nlinarith only [hh, hx', hy', hsum]
/-- Insert the missing mass at zero trace excess, then separate the normalizer
error and both powers of the source error. The constant precedes every weight. -/
theorem transport_penalty_convex_error (Q : ℕ) (hQ : 1 ≤ Q) (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type*) (s : Finset ι) (lam x : ι → ℝ),
      (∀ i ∈ s, 0 ≤ lam i) → (∀ i ∈ s, 0 ≤ x i) → (∑ i ∈ s, lam i) ≤ 1 →
      ∀ δ u t : ℝ, δ ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ u → 0 ≤ t →
      t ≤ (4 / 3 : ℝ) * (∑ i ∈ s, lam i * x i) + (D * δ + u) →
      (1 + t) ^ Q - 1 ≤ C * ((∑ i ∈ s, lam i * ((1 + x i) ^ Q - 1)) + δ + u + u ^ Q) := by
  let a : ℝ := 2 ^ Q
  let b : ℝ := 3 ^ Q
  let c : ℝ := (max 1 D) ^ Q
  let C := a * b + a * a * c * a * 2 + a * a * a + 1
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ι s lam x hlam hx hmass δ u t hδ hu ht hbound
  let X := ∑ i ∈ s, lam i * x i
  let M := ∑ i ∈ s, lam i * ((1 + x i) ^ Q - 1)
  have hX : 0 ≤ X := Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi) (hx i hi)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i hi => mul_nonneg (hlam i hi)
    (sub_nonneg.mpr (one_le_pow₀ (by linarith only [hx i hi])))
  have hcx := meanPenalty_convex_combination Q s lam x hlam hx hmass
  have hpx : (1 + (4 / 3 : ℝ) * X) ^ Q - 1 ≤ b * M := by
    calc
      _ ≤ (1 + 3 * X) ^ Q - 1 := sub_le_sub_right (pow_le_pow_left₀ (by positivity) (by linarith
        only [hX]) Q) 1
      _ ≤ b * ((1 + X) ^ Q - 1) := transport_penalty_scale Q hX (by norm_num)
      _ ≤ b * M := mul_le_mul_of_nonneg_left hcx hb.le
  have hδpow : δ ^ Q ≤ δ := by
    have hh := pow_le_pow_left₀ hδ.1 hδ.2 (Q - 1)
    rw [one_pow] at hh
    calc
      _ = δ ^ (Q - 1) * δ := by rw [← pow_succ, Nat.sub_add_cancel hQ]
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hh hδ.1
      _ = δ := one_mul δ
  have hpδ : (1 + D * δ) ^ Q - 1 ≤ c * a * 2 * δ := by
    calc
      _ ≤ (1 + max 1 D * δ) ^ Q - 1 := sub_le_sub_right
        (pow_le_pow_left₀ (add_nonneg zero_le_one (mul_nonneg hD hδ.1)) (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (le_max_right 1 D) hδ.1)) Q) 1
      _ ≤ c * ((1 + δ) ^ Q - 1) := transport_penalty_scale Q hδ.1 (le_max_left 1 D)
      _ ≤ c * (a * (δ + δ ^ Q)) := mul_le_mul_of_nonneg_left (transport_penalty_linear_and_power
        Q hδ.1) hc.le
      _ ≤ c * (a * (δ + δ)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hδpow) ha.le) hc.le
      _ = _ := by ring
  have hpu := transport_penalty_linear_and_power Q hu
  have hsplit := transport_penalty_add Q (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hX)
    (add_nonneg (mul_nonneg hD hδ.1) hu)
  have hsplit' := transport_penalty_add Q (mul_nonneg hD hδ.1) hu
  have hfirst : (1 + t) ^ Q - 1 ≤ a * (b * M + a * (c * a * 2 * δ + a * (u + u ^ Q))) := by
    apply (sub_le_sub_right (pow_le_pow_left₀ (by linarith only [ht]) (add_le_add le_rfl hbound)
      Q) 1).trans
    apply hsplit.trans
    apply mul_le_mul_of_nonneg_left _ ha.le
    apply add_le_add hpx
    exact hsplit'.trans (mul_le_mul_of_nonneg_left (add_le_add hpδ hpu) ha.le)
  have h1 : 0 ≤ a * b := by positivity
  have h2 : 0 ≤ a * a * c * a * 2 := by positivity
  have h3 : 0 ≤ a * a * a := by positivity
  have hCa : a * b ≤ C := by dsimp only [C]; linarith only [h2, h3]
  have hCb : a * a * c * a * 2 ≤ C := by dsimp only [C]; linarith only [h1, h3]
  have hCc : a * a * a ≤ C := by dsimp only [C]; linarith only [h1, h2]
  calc
    _ ≤ _ := hfirst
    _ = a * b * M + (a * a * c * a * 2) * δ + (a * a * a) * (u + u ^ Q) := by ring
    _ ≤ C * M + C * δ + C * (u + u ^ Q) := add_le_add (add_le_add (mul_le_mul_of_nonneg_right
      hCa hM) (mul_le_mul_of_nonneg_right hCb hδ.1))
      (mul_le_mul_of_nonneg_right hCc (add_nonneg hu (pow_nonneg hu Q)))
    _ = _ := by dsimp only [M]; ring
/-- The expectation of the actual Whitney sum is the finite weighted sum of
stationary row means plus the expectation of the fine subseries. -/
theorem transport_whitney_mean_identity (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger
      P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (W : Set (Vec d)) (cap
      : ℤ) (hcap : (jStar : ℤ) ≤ cap)
    (hfin : ∀ t ≤ cap, (maximalAdaptedCellCenters W (explicitRoundedGrid jStar m) cap t).Finite)
    (N : ℝ) (hN : 1 ≤ N) (R : BlockMat d) :
    let q := explicitRoundedGrid jStar m
    let I := {p : ℤ × (Fin d → ℤ) // IsMaximalAdaptedCellIn W q cap p.1 p.2}
    let f := fun (p : I) a => ((volume (adaptedCellAtCenter q p.1.1 p.1.2)).toReal / (volume
      W).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellAtCenter q p.1.1 p.1.2) a)
    let Z := fun t => if ht : t ≤ cap then (hfin t ht).toFinset else ∅
    let lam := fun t => ∑ _z ∈ Z t, (volume (adaptedCell q t)).toReal / (volume W).toReal
    let G := fun a => normalizedBlock (ofFullBlockMat (∑' p, f p a)) R
    let T := fun a => normalizedBlock (ofFullBlockMat (∑' p : {p : I // p.1.1 < (jStar : ℤ)}, f
      p a)) R
    SchattenMemLp P N T → (∀ᵐ a ∂P, Summable (fun p => f p a)) →
    toFullBlockMat (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)) =
      (∑ t ∈ Finset.Icc (jStar : ℤ) cap, lam t • toFullBlockMat (normalizedBlock (adaptedMean P
        q t) R)) +
      toFullBlockMat (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (T a) α β ∂P)) := by
  intro q I f Z lam G T hT hseries
  let row := fun t a => normalizedBlock (ofFullBlockMat (∑ z ∈ Z t,
    ((volume (adaptedCell q t)).toReal / (volume W).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellTranslate q t z) a))) R
  let J := Finset.Icc (jStar : ℤ) cap
  have hmem (t : ℤ) : SchattenMemLp P N (row t) := Source.memLqSchatten_normalizedBlock
    (Source.memLqSchatten_finset_sum hN (Z t) (fun _ => (volume (adaptedCell q t)).toReal /
      (volume W).toReal)
      (fun z a => coarseBlock (adaptedCellTranslate q t z) a)
      (fun z _ => Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hjStar m hm t z N hN)) hN R
  have hdecomp : ∀ᵐ a ∂P, toFullBlockMat (G a) = (∑ t ∈ J, toFullBlockMat (row t a)) +
    toFullBlockMat (T a) := by
    filter_upwards [hseries] with a ha
    have hc : cap ∈ J := Finset.mem_Icc.mpr ⟨hcap, le_rfl⟩
    have he : J.erase cap = Finset.Icc (jStar : ℤ) (cap - 1) := by
      ext t; simp only [J, Finset.mem_erase, Finset.mem_Icc]; omega
    rw [← Finset.sum_erase_add _ _ hc, he, add_comm (∑ t ∈ _, _)]; exact
      transport_whitney_raw_split q (isUnit_roundedGrid hjStar hm) W jStar cap hcap hfin a R ha
  have hmean := transport_mean_finite_split hN J row G T (fun t _ => hmem t) hT hdecomp
  apply hmean.trans
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have htl := (Finset.mem_Icc.mp ht).1
  have htu := (Finset.mem_Icc.mp ht).2
  have hz (z) (hz : z ∈ Z t) : z ∈ adaptedLatticeAtScale q t := by
    have h : z ∈ maximalAdaptedCellCenters W q cap t := (hfin t htu).mem_toFinset.mp (by simpa
      only [Z, dite_eq_left htu] using hz)
    rcases h with ⟨v, _hv, rfl⟩
    exact ⟨v, rfl⟩
  have hmrow := (transport_centered_lattice_row d hd P γ E Ψ K S hstat hdag jStar hjStar m hm
    t htl (Z t) hz (fun _ => (volume (adaptedCell q t)).toReal / (volume W).toReal) R).1
  calc
    _ = toFullBlockMat (blockScale (lam t) (normalizedBlock (adaptedMean P q t) R)) := congrArg
      toFullBlockMat hmrow
    _ = _ := by ext (α | α) (β | β) <;> rfl

end
end HCPolySupport.HighContrast.Annealed
