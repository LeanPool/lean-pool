/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.ExponentAndLossArithmetic

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.MeanPenaltyDrift

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The trace inequality, the mean penalty and drift positivity

Group C of the printed proof (`p.fixed.geometry.one.grid.propagation`): the positive-semidefinite
trace inequality, composition and advance of the mean penalty, its exponential bound, the
loss/trace comparison, and nonnegativity of the determinant drift.

Part of the proof of the printed proposition `p.fixed.geometry.one.grid.propagation`, stated in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group: `q = 𝒬(𝔪)` is
`Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift; `metric` (not
`m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the source lower scale
`e.source.lower.scale` is carried exactly by `HCPoly/Entry/OneGridPropagation.lean`; this
group's stronger internal algebraic and history lemmas omit an unused threshold on the source
lower scale, and this group's generic integration helpers take finiteness, integrability or
measurability inputs that are proved at their actual use sites, not extra premises of the
printed proposition.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockLogDet blockSub blockTrace matSqrt
  matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group C. The printed trace inequality, the mean penalty and drift positivity
(`p.fixed.geometry.one.grid.propagation`) -/

/-- `tr(AB) ≤ (tr A)(tr B)` for positive semidefinite `A`, `B`: the positivity step behind the
printed trace inequality (`p.fixed.geometry.one.grid.propagation`). -/
theorem trace_mul_le_trace_mul_trace {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace ≤ A.trace * B.trace := by
  classical
  open scoped MatrixOrder in
  have hbound : B ≤ B.trace • (1 : Matrix ι ι ℝ) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    apply le_algebraMap_of_spectrum_le (ha := hB.isHermitian)
    intro x hx
    obtain ⟨i, rfl⟩ := hB.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hroot := matSqrt_spec hA
  have hpos := (Matrix.le_iff.mp hbound).conjTranspose_mul_mul_same (matSqrt A)
  have htr := hpos.trace_nonneg
  rw [hroot.1.isHermitian.eq, Matrix.trace_mul_cycle, hroot.2,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, mul_one,
    Matrix.trace_smul, smul_eq_mul] at htr
  linarith only [htr]

/-- The printed composition of mean penalties across a change of normalization
(`p.fixed.geometry.one.grid.propagation`):
`1 + Ψ_Q(P^q_{j,m}) ≤ (1 + Ψ_Q(P^q_{n,m}))(1 + Ψ_Q(P^q_{j,n}))`. -/
theorem meanPenalty_normalizedMean_compose (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ j n m : ℤ, (jStar : ℤ) ≤ j → j ≤ n → n ≤ m →
            1 + meanPenalty (bigQ d γ)
                (relMean P (Geometry.explicitRoundedGrid jStar metric) j m) ≤
              (1 + meanPenalty (bigQ d γ)
                  (relMean P (Geometry.explicitRoundedGrid jStar metric) n m)) *
                (1 + meanPenalty (bigQ d γ)
                  (relMean P (Geometry.explicitRoundedGrid jStar metric) j n)) := by
  intro P E Ψ K S hP hstat _hunit hdag jStar hjStar metric hmetric j n m hj hjn hnm
  let := hP
  let F := toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) j)
  let G := toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) n)
  let H := toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) m)
  have hF : F.PosDef := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric j
  have hG : G.PosDef := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n
  have hH : H.PosDef := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric m
  open scoped MatrixOrder in
  have hGF : G ≤ F := (Annealed.fullBlock_le_iff hG.isHermitian hF.isHermitian).2
    (Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric j n hj hjn)
  open scoped MatrixOrder in
  have hHG : H ≤ G := (Annealed.fullBlock_le_iff hH.isHermitian hG.isHermitian).2
    (Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m (hj.trans hjn) hnm)
  have hGiG := Matrix.nonsing_inv_mul G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)
  have hHiH := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hHHi := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hinv : (H⁻¹ - G⁻¹).PosSemidef := by
    have hD := hH.inv.isHermitian.sub hG.inv.isHermitian
    have h₁ := hH.posSemidef.conjTranspose_mul_mul_same (H⁻¹ - G⁻¹)
    have h₂ := (Matrix.le_iff.mp hHG).conjTranspose_mul_mul_same G⁻¹
    rw [hD.eq] at h₁
    rw [hG.inv.isHermitian.eq] at h₂
    convert h₁.add h₂ using 1
    simp only [mul_sub, sub_mul, hHiH, hGiG, one_mul]
    rw [mul_assoc G⁻¹ H H⁻¹, hHHi, mul_one]
    abel
  let T := matSqrt G⁻¹
  let R := T⁻¹
  have hT : T.PosDef := matSqrt_inv_posDef_full hG
  have hRT : R * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  have hTR : T * R = 1 := Matrix.mul_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  have hTT : T * T = G⁻¹ := (matSqrt_spec hG.inv.posSemidef).2
  have hTGT : T * G * T = 1 := matSqrt_inv_conj hG
  have hRR : R * R = G := by
    calc
      R * R = R * (T * G * T) * R := by rw [hTGT, mul_one]
      _ = (R * T) * G * (T * R) := by simp only [mul_assoc]
      _ = G := by rw [hRT, hTR, one_mul, mul_one]
  let U := T * F * T - 1
  let V := R * H⁻¹ * R - 1
  have hU : U.PosSemidef := Matrix.le_iff.mp (Recurrence.one_le_normalize hG hGF)
  have hV : V.PosSemidef := by
    have hv := hinv.conjTranspose_mul_mul_same R
    have hR : R.IsHermitian := hT.inv.isHermitian
    rw [hR.eq] at hv
    have hcancel : R * G⁻¹ * R = 1 := by
      rw [← hTT]
      simp only [← mul_assoc, hRT, one_mul, hTR]
    simpa only [mul_sub, sub_mul, hcancel, V] using hv
  have htrace (A B : FullBlockMat d) (hB : B.PosDef) :
      (matSqrt B⁻¹ * A * matSqrt B⁻¹).trace = (B⁻¹ * A).trace := by
    rw [Matrix.trace_mul_cycle, (matSqrt_spec hB.inv.posSemidef).2]
  have hW : (R * H⁻¹ * R).trace = (H⁻¹ * G).trace := by
    rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
  have hprod : (T * F * T * (R * H⁻¹ * R)).trace = (H⁻¹ * F).trace := by
    have heq : T * F * T * (R * H⁻¹ * R) = T * F * H⁻¹ * R := by
      simp only [mul_assoc, ← mul_assoc T R, hTR, one_mul]
    rw [heq, Matrix.trace_mul_comm _ R]
    simp only [← mul_assoc, hRT, one_mul]
    exact Matrix.trace_mul_comm _ _
  have htr := trace_mul_le_trace_mul_trace hU hV
  have htU : U.trace = (G⁻¹ * F).trace - (1 : FullBlockMat d).trace := by
    change (T * F * T - 1).trace = _
    rw [Matrix.trace_sub, htrace F G hG]
  have htV : V.trace = (H⁻¹ * G).trace - (1 : FullBlockMat d).trace := by
    change (R * H⁻¹ * R - 1).trace = _
    rw [Matrix.trace_sub, hW]
  have htUV : (U * V).trace = (H⁻¹ * F).trace - (G⁻¹ * F).trace -
      (H⁻¹ * G).trace + (1 : FullBlockMat d).trace := by
    simp only [U, V, mul_sub, sub_mul, mul_one, one_mul, Matrix.trace_sub]
    rw [hprod, htrace F G hG, hW]
    ring
  have hscalar : 1 + ((H⁻¹ * F).trace - (1 : FullBlockMat d).trace) ≤
      (1 + ((H⁻¹ * G).trace - (1 : FullBlockMat d).trace)) *
        (1 + ((G⁻¹ * F).trace - (1 : FullBlockMat d).trace)) := by
    rw [htU, htV, htUV] at htr
    nlinarith only [htr]
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hsub (A B : BlockMat d) : toFullBlockMat (blockSub A B) =
      toFullBlockMat A - toFullBlockMat B := by
    ext α β
    cases α <;> cases β <;> rfl
  have ht (a b : ℤ) (hb : (toFullBlockMat (adaptedMean P
      (Geometry.explicitRoundedGrid jStar metric) b)).PosDef) :
      blockTrace (blockSub (relMean P (Geometry.explicitRoundedGrid jStar metric) a b)
        (Book.Ch02.blockIdentity d)) =
      ((toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) b))⁻¹ *
        toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) a)).trace -
        (1 : FullBlockMat d).trace := by
    rw [blockTrace, hsub, hI, Matrix.trace_sub, relMean, normalizedBlock,
      toFullBlockMat_ofFullBlockMat, htrace _ _ hb]
  have hscalar' : 1 + blockTrace (blockSub (relMean P
      (Geometry.explicitRoundedGrid jStar metric) j m) (Book.Ch02.blockIdentity d)) ≤
      (1 + blockTrace (blockSub (relMean P
        (Geometry.explicitRoundedGrid jStar metric) n m) (Book.Ch02.blockIdentity d))) *
      (1 + blockTrace (blockSub (relMean P
        (Geometry.explicitRoundedGrid jStar metric) j n) (Book.Ch02.blockIdentity d))) := by
    simpa only [ht j m hH, ht n m hH, ht j n hG] using hscalar
  have hnn : 0 ≤ 1 + blockTrace (blockSub (relMean P
      (Geometry.explicitRoundedGrid jStar metric) j m) (Book.Ch02.blockIdentity d)) := by
    have hmean := Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric j m hj (hjn.trans hnm)
    have hsym := Analysis.toFullBlockMat_isHermitian_iff
      (relMean P (Geometry.explicitRoundedGrid jStar metric) j m)
    have hp := Annealed.normalizedBlock_posDef _ _ hF hH
    have hnonneg := Analysis.blockTrace_identity_sub_nonneg _ (hsym.mp hp.isHermitian) hmean.1
    linarith only [hnonneg]
  have hpow := pow_le_pow_left₀ hnn hscalar' (bigQ d γ)
  rw [mul_pow] at hpow
  simp only [meanPenalty]
  convert hpow using 1 <;> first | rfl | ring

/-- The mean-penalty advance used in Steps 2 and 4 (`p.fixed.geometry.one.grid.propagation`):
`Ψ_Q(P^q_{j,k}) ≤ e^{QΔ^q_{m,k}}Ψ_Q(P^q_{j,m}) + e^{QΔ^q_{m,k}} - 1` for `j ≤ m ≤ k`. -/
theorem meanPenalty_normalizedMean_advance (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ j m k : ℤ, (jStar : ℤ) ≤ j → j ≤ m → m ≤ k →
            meanPenalty (bigQ d γ)
                (relMean P (Geometry.explicitRoundedGrid jStar metric) j k) ≤
              Real.exp ((bigQ d γ : ℝ) *
                    detIncrement P (Geometry.explicitRoundedGrid jStar metric) m k) *
                  meanPenalty (bigQ d γ)
                    (relMean P (Geometry.explicitRoundedGrid jStar metric) j m) +
                Real.exp ((bigQ d γ : ℝ) *
                  detIncrement P (Geometry.explicitRoundedGrid jStar metric) m k) - 1 := by
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric j m k hj hjm hmk
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hcomp := meanPenalty_normalizedMean_compose d hd γ hγ P E Ψ K S hP hstat
    hunit hdag jStar hjStar metric hmetric j m k hj hjm hmk
  have hp := Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric m k (hj.trans hjm) hmk
  have hpjm := Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric j m hj hjm
  have hpos := Annealed.normalizedBlock_posDef _ _
    (Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric m)
    (Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric k)
  have ht : 0 ≤ blockTrace (blockSub (relMean P q m k) (Book.Ch02.blockIdentity d)) :=
    Analysis.blockTrace_identity_sub_nonneg _
      ((Analysis.toFullBlockMat_isHermitian_iff _).mp hpos.isHermitian) hp.1
  have hbound : 1 + meanPenalty (bigQ d γ) (relMean P q m k) ≤
      Real.exp ((bigQ d γ : ℝ) * detIncrement P q m k) := by
    have hbase : 1 + blockTrace (blockSub (relMean P q m k)
        (Book.Ch02.blockIdentity d)) ≤ Real.exp (detIncrement P q m k) := by
      linarith only [hp.2.2.2.2.1]
    have hpow := pow_le_pow_left₀ (by linarith only [ht] :
      0 ≤ 1 + blockTrace (blockSub (relMean P q m k) (Book.Ch02.blockIdentity d)))
      hbase (bigQ d γ)
    rw [← Real.exp_nat_mul] at hpow
    unfold meanPenalty
    linarith only [hpow]
  have hmul := mul_le_mul_of_nonneg_right hbound
    (by linarith only [hpjm.2.2.2.2.2] : 0 ≤ 1 + meanPenalty (bigQ d γ) (relMean P q j m))
  nlinarith only [hcomp, hmul]

/-- `Ψ_Q(P^q_{j,k}) ≤ e^{QΔ^q_{j,k}} - 1`, the bound used for the generations above the base
(`p.fixed.geometry.one.grid.propagation`). -/
theorem meanPenalty_normalizedMean_le_exp_sub_one (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ j k : ℤ, (jStar : ℤ) ≤ j → j ≤ k →
            meanPenalty (bigQ d γ)
                (relMean P (Geometry.explicitRoundedGrid jStar metric) j k) ≤
              Real.exp ((bigQ d γ : ℝ) *
                detIncrement P (Geometry.explicitRoundedGrid jStar metric) j k) - 1 := by
  intro P E Ψ K S hP hstat hunit hdag jStar hjStar metric hmetric j k hj hjk
  let := hP
  have h := meanPenalty_normalizedMean_advance d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric j j k hj le_rfl hjk
  rw [Annealed.normalizedMean_self d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric j, meanPenalty_identity, mul_zero, zero_add] at h
  exact h

/-- `Δ^q_{j,k} ≤ tr(P^q_{j,k} - I_{2d})` (`p.fixed.geometry.one.grid.propagation`), the step that
converts a loss into a
profile term in Step 4. -/
theorem logDetLoss_le_blockTrace_normalizedMean (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ j k : ℤ, (jStar : ℤ) ≤ j → j ≤ k →
            detIncrement P (Geometry.explicitRoundedGrid jStar metric) j k ≤
              blockTrace (blockSub
                (relMean P (Geometry.explicitRoundedGrid jStar metric) j k)
                (Book.Ch02.blockIdentity d)) := by
  intro P E Ψ K S hP hstat _hunit hdag jStar hjStar metric hmetric j k _hj _hjk
  let := hP
  have hF := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric j
  have hG := Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric k
  have hp : (toFullBlockMat (relMean P (Geometry.explicitRoundedGrid jStar metric) j k)).PosDef :=
    Annealed.normalizedBlock_posDef _ _ hF hG
  have heig : ∀ i, 0 < hp.isHermitian.eigenvalues i := hp.eigenvalues_pos
  have hlog := blockLogDet_normalizedMean_eq_loss P
    (Geometry.explicitRoundedGrid jStar metric) j k hF hG
  rw [← hlog, blockLogDet, hp.isHermitian.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (heig i))]
  have hI : toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
    ext α β
    cases α <;> cases β <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]
  have hsub (A B : BlockMat d) : toFullBlockMat (blockSub A B) =
      toFullBlockMat A - toFullBlockMat B := by
    ext α β
    cases α <;> cases β <;> rfl
  rw [blockTrace, hsub, hI, Matrix.trace_sub, hp.isHermitian.trace_eq_sum_eigenvalues]
  rw [Matrix.trace_one]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (heig i))
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using! h


/-- The determinant drift is nonnegative: each printed increment `P^q_{j-1,m} - P^q_{j,m}` is a
normalized positive semidefinite increment, and the weights are positive. -/
theorem determinantDrift_nonneg (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) :
    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
      (S : CoeffSpace d → ℝ),
      IsProbabilityMeasure P →
      IsStationaryLaw P →
      IsUnitRangeLaw P →
      CoarseEllipticityDagger P γ E Ψ K S →
      ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
        ∀ (metric : Mat d), metric.PosDef →
          ∀ m : ℤ, 0 ≤ determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m
            := by
  intro P E Ψ K S hprob hstat _hunit hdag jStar hjStar metric hmetric m
  let : IsProbabilityMeasure P := hprob
  unfold determinantDrift
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg
  · exact Real.rpow_nonneg (by norm_num) _
  · have hj' := Finset.mem_Icc.mp hj
    rw [relMean, relMean]
    have hF : (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric)
      m)).PosDef :=
      HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar
        hjStar metric hmetric m
    have horder : BlockMatLoewnerLE
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) j)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) (j - 1)) :=
      HCPolySupport.HighContrast.Annealed.adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar
        hjStar metric hmetric (j - 1) j (by omega) (by omega)
    have hJ : (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric)
      j)).PosDef :=
      HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar
        hjStar metric hmetric j
    have hJm1 : (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) (j -
      1))).PosDef :=
      HCPolySupport.HighContrast.Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar
        hjStar metric hmetric (j - 1)
    have hsub_full (A B : BlockMat d) : toFullBlockMat (blockSub A B) = toFullBlockMat A -
      toFullBlockMat B := by
      ext α β
      cases α <;> cases β <;> rfl
    have hgap : (toFullBlockMat (blockSub
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) (j - 1))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) j))).PosSemidef := by
      rw [hsub_full]
      apply Matrix.le_iff.mp
      rw [Matrix.le_iff]
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hJm1.isHermitian.sub hJ.isHermitian) ?_
      intro x
      have hq := horder (ofFullBlockVec x)
      simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
        toFullBlockVec_ofFullBlockVec] at hq
      simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
      linarith only [hq]
    have hnorm : 0 ≤ blockTrace (normalizedBlock (blockSub
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) (j - 1))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) j))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) m)) := by
      have h := hgap.conjTranspose_mul_mul_same
        (matSqrt (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) m))⁻¹)
      rw [(matSqrt_inv_posDef_full hF).isHermitian.eq] at h
      simpa only [blockTrace, normalizedBlock, toFullBlockMat_ofFullBlockMat] using h.trace_nonneg
    have htrace_eq : blockTrace (blockSub
        (normalizedBlock (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) (j - 1))
          (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) m))
        (normalizedBlock (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) j)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) m))) =
        blockTrace (normalizedBlock (blockSub
          (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) (j - 1))
          (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) j))
          (adaptedMean P (Geometry.explicitRoundedGrid jStar metric) m)) := by
      simp only [blockTrace, hsub_full, normalizedBlock, toFullBlockMat_ofFullBlockMat,
        Matrix.mul_sub, Matrix.sub_mul]
    rwa [htrace_eq]

end

end HCPolySupport.HighContrast.Multiscale
