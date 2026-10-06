/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.FullBlockSharpHarmonic
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AlignedSubdivisionQuadraticGap
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastVarianceCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The abstract variance split

The pathwise chain of Lemma 4.4 of HC as a pure matrix estimate: a positive
parent below the average of positive children, dominating its sharp, has
normalized distance to the terminal frame controlled by the children's
average fluctuation around the intermediate frame plus the sharp-gap and
dilation terms.  All anchors are abstract, so the estimate applies
unchanged at the recentered (hatted) objects, where the two frame-sensitive
scalar inputs are dischargeable.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem conj_herm' {N X : FullBlockMat d} (hN : Nᴴ = N)
    (hX : Xᴴ = X) : (N * X * N)ᴴ = N * X * N := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hN, hX]
  noncomm_ring

private theorem conj_mono' {X Y : FullBlockMat d}
    (h : X ≤ Y) : ∀ M : FullBlockMat d, Mᴴ * X * M ≤ Mᴴ * Y * M := by
  intro M
  have hpsd : (Y - X).PosSemidef := Matrix.le_iff.mp h
  have hconj := hpsd.conjTranspose_mul_mul_same M
  refine Matrix.le_iff.mpr ?_
  have hrw : Mᴴ * (Y - X) * M = Mᴴ * Y * M - Mᴴ * X * M := by
    noncomm_ring
  rwa [hrw] at hconj

private theorem norm_le_norm_of_psd_le' {X Y : FullBlockMat d}
    (hX : Xᴴ = X) (hX0 : (0 : FullBlockMat d) ≤ X) (hXY : X ≤ Y)
    (hY : Yᴴ = Y) : ‖X‖ ≤ ‖Y‖ := by
  refine PortableHistory.norm_le_of_sandwich hX (norm_nonneg Y) ?_ ?_
  · refine hXY.trans ?_
    exact (PortableHistory.sandwich_of_norm_le hY (le_refl ‖Y‖)).1
  · refine le_trans ?_ hX0
    have h1 : (0 : FullBlockMat d) ≤ ‖Y‖ • (1 : FullBlockMat d) := by
      refine Matrix.le_iff.mpr ?_
      rw [sub_zero]
      exact (Matrix.PosSemidef.one).smul (norm_nonneg Y)
    have h2 := neg_le_neg h1
    simpa only [neg_zero, neg_smul] using h2

private theorem average_parent_gap_le_sharp_fluctuation
    {ι : Type*} [DecidableEq ι] (Z : Finset ι) (hZne : Z.Nonempty)
    (A : ι → FullBlockMat d) (hA : ∀ i ∈ Z, (A i).PosDef)
    {Ap Gj avgA : FullBlockMat d} (hAp : Ap.PosDef) (hGj : Gj.PosDef)
    (havgAdef : avgA = (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, A i)
    (hparentLe : Ap ≤ avgA) (hparentSharp : fullBlockSharp Ap ≤ Ap)
    (hGjherm : Gjᴴ = Gj) :
    avgA - Ap ≤ (Z.card : ℝ)⁻¹ •
      ∑ i ∈ Z, fullBlockSharpFluctuation (A i) Gj := by
  classical
  have hgap2 : avgA - Ap ≤ (Z.card : ℝ)⁻¹ •
      ∑ i ∈ Z, fullBlockSharpFluctuation (A i) Gj := by
    have hGjsymm : Gj.IsSymm := isSymm_of_isHermitian hGjherm
    have hsharpGap := fullBlockFinsetAverage_sharp_sub_parentSharp_le_averageQuadratic
      Z hZne A Gj Ap hA hGjsymm hAp (by rw [← havgAdef]; exact hparentLe)
    have hpre : ((Z.card : ℝ)⁻¹ • ∑ i ∈ Z, fullBlockSharp (A i) - Ap) +
        (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, (A i - fullBlockSharp (A i)) ≤
        (Z.card : ℝ)⁻¹ •
          (∑ i ∈ Z, (fullBlockSharp (A i) - Gj) *
            (fullBlockSharp (A i))⁻¹ * (fullBlockSharp (A i) - Gj)) +
        (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, (A i - fullBlockSharp (A i)) := by
      refine add_le_add ?_ le_rfl
      have h1 : (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, fullBlockSharp (A i) - Ap ≤
          (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, fullBlockSharp (A i) -
            fullBlockSharp Ap := by
        exact sub_le_sub_left hparentSharp _
      exact h1.trans hsharpGap
    have hsplitavg : avgA - Ap =
        ((Z.card : ℝ)⁻¹ • ∑ i ∈ Z, fullBlockSharp (A i) - Ap) +
          (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, (A i - fullBlockSharp (A i)) := by
      rw [havgAdef, Finset.sum_sub_distrib, smul_sub]
      abel
    have hfluctsplit : (Z.card : ℝ)⁻¹ •
        ∑ i ∈ Z, fullBlockSharpFluctuation (A i) Gj =
        (Z.card : ℝ)⁻¹ •
          (∑ i ∈ Z, (fullBlockSharp (A i) - Gj) *
            (fullBlockSharp (A i))⁻¹ * (fullBlockSharp (A i) - Gj)) +
        (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, (A i - fullBlockSharp (A i)) := by
      rw [← smul_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact (fullBlockSharp_quadratic_add_primal_sub_eq_fluctuation
        (hA i hi) hGj).symm
    rw [hsplitavg, hfluctsplit]
    exact hpre
  exact hgap2

private theorem average_sharp_fluctuation_expansion
    {ι : Type*} [DecidableEq ι] (Z : Finset ι)
    (A : ι → FullBlockMat d) (hA : ∀ i ∈ Z, (A i).PosDef)
    {Gj R avgA : FullBlockMat d}
    (hRdef : R = fullBlockRefl d)
    (havgAdef : avgA = (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, A i)
    (hcard0 : (Z.card : ℝ) ≠ 0) :
    (Z.card : ℝ)⁻¹ •
      ∑ i ∈ Z, fullBlockSharpFluctuation (A i) Gj =
      (avgA - Gj) + Gj * R * (avgA - Gj) * R * Gj +
        Gj * R * (Gj - fullBlockSharp Gj) * R * Gj := by
  classical
  have hGjinv : Gj⁻¹ = R * fullBlockSharp Gj * R := by
    have h : R * fullBlockSharp Gj * R = Gj⁻¹ := by
      rw [fullBlockSharp, hRdef]
      calc fullBlockRefl d * (fullBlockRefl d * Gj⁻¹ * fullBlockRefl d) *
          fullBlockRefl d =
          (fullBlockRefl d * fullBlockRefl d) * Gj⁻¹ *
            (fullBlockRefl d * fullBlockRefl d) := by noncomm_ring
        _ = Gj⁻¹ := by
            rw [fullBlockRefl_mul_self, Matrix.one_mul, Matrix.mul_one]
    exact h.symm
  have hfluct_w : ∀ i ∈ Z,
      fullBlockSharpFluctuation (A i) Gj =
      (A i - Gj) + Gj * R * (A i - Gj) * R * Gj +
        Gj * R * (Gj - fullBlockSharp Gj) * R * Gj := by
    intro i hi
    rw [fullBlockSharpFluctuation, fullBlockSharp_inv (hA i hi), hGjinv,
      hRdef]
    noncomm_ring
  have hsum : ∑ i ∈ Z, fullBlockSharpFluctuation (A i) Gj =
      (∑ i ∈ Z, (A i - Gj)) +
        Gj * R * (∑ i ∈ Z, (A i - Gj)) * R * Gj +
        (Z.card : ℝ) • (Gj * R * (Gj - fullBlockSharp Gj) * R * Gj) := by
    rw [Finset.sum_congr rfl hfluct_w, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    congr 1
    · congr 1
      refine Eq.symm ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    · rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have havgsub : avgA - Gj = (Z.card : ℝ)⁻¹ •
      ∑ i ∈ Z, (A i - Gj) := by
    rw [havgAdef, Finset.sum_sub_distrib, smul_sub, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard0,
      one_smul]
  have hburrito : (Z.card : ℝ)⁻¹ •
      ∑ i ∈ Z, fullBlockSharpFluctuation (A i) Gj =
      (avgA - Gj) + Gj * R * (avgA - Gj) * R * Gj +
        Gj * R * (Gj - fullBlockSharp Gj) * R * Gj := by
    rw [hsum, smul_add, smul_add, havgsub]
    congr 1
    · congr 1
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    · rw [smul_smul, inv_mul_cancel₀ hcard0, one_smul]
  exact hburrito

private theorem normalized_conjugator_norm_squared_bound [NeZero d]
    {Gp Gj N R M : FullBlockMat d} (hGp : Gp.PosDef) (hGj : Gj.PosDef)
    {cH cD : ℝ} (hcH0 : 0 ≤ cH) (hcD0 : 0 ≤ cD)
    (hsharpPinv : (fullBlockSharp Gp)⁻¹ ≤ cH • Gp⁻¹)
    (hdil : Gj ≤ (1 + cD) • Gp)
    (hNherm : Nᴴ = N) (hGjherm : Gjᴴ = Gj)
    (hNGpN : N * Gp * N = 1) (hNN : N * N = Gp⁻¹)
    (hMdef : M = N * Gj * R * matSqrt Gp)
    (hMherm : Mᴴ = matSqrt Gp * R * Gj * N)
    (hsqGp : matSqrt Gp * matSqrt Gp = Gp) (hRdef : R = fullBlockRefl d) :
    ‖M‖ ^ 2 ≤ cH * (1 + cD) ^ 2 := by
  classical
  have hNGjN_le : N * Gj * N ≤ (1 + cD) • (1 : FullBlockMat d) := by
    have h := conj_mono' hdil N
    rw [hNherm] at h
    refine h.trans (le_of_eq ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul, hNGpN]
  have hNGjN0 : (0 : FullBlockMat d) ≤ N * Gj * N := by
    have hpsd : (0 : FullBlockMat d) ≤ Gj := by
      refine Matrix.le_iff.mpr ?_
      rw [sub_zero]
      exact hGj.posSemidef
    have h := conj_mono' hpsd N
    have h0 : N * 0 * N = (0 : FullBlockMat d) := by noncomm_ring
    rw [hNherm, h0] at h
    exact h
  have hNGjNherm : (N * Gj * N)ᴴ = N * Gj * N := conj_herm' hNherm hGjherm
  have hNGjNnorm : ‖N * Gj * N‖ ≤ 1 + cD := by
    refine PortableHistory.norm_le_of_sandwich hNGjNherm (by linarith only [hcD0])
      hNGjN_le ?_
    refine le_trans ?_ hNGjN0
    have h1 : (0 : FullBlockMat d) ≤ (1 + cD) • (1 : FullBlockMat d) := by
      refine Matrix.le_iff.mpr ?_
      rw [sub_zero]
      exact Matrix.PosSemidef.one.smul (by linarith only [hcD0])
    have h2 := neg_le_neg h1
    simpa only [neg_zero, neg_smul] using h2
  have hMMt : M * Mᴴ = N * Gj * (R * Gp * R) * Gj * N := by
    rw [hMdef, hMherm]
    calc N * Gj * R * matSqrt Gp * (matSqrt Gp * R * Gj * N) =
        N * Gj * R * (matSqrt Gp * matSqrt Gp) * R * Gj * N := by
          noncomm_ring
      _ = N * Gj * (R * Gp * R) * Gj * N := by
          rw [hsqGp]
          noncomm_ring
  have hRGpR : R * Gp * R = (fullBlockSharp Gp)⁻¹ := by
    rw [fullBlockSharp_inv hGp, hRdef]
  have hMMt_le : M * Mᴴ ≤ cH • ((N * Gj * N) * (N * Gj * N)) := by
    rw [hMMt, hRGpR]
    have hconj := conj_mono' hsharpPinv (Gj * N)
    have hlhs : (Gj * N)ᴴ * (fullBlockSharp Gp)⁻¹ * (Gj * N) =
        N * Gj * (fullBlockSharp Gp)⁻¹ * Gj * N := by
      rw [Matrix.conjTranspose_mul, hNherm, hGjherm]
      noncomm_ring
    have hrhs : (Gj * N)ᴴ * (cH • Gp⁻¹) * (Gj * N) =
        cH • ((N * Gj * N) * (N * Gj * N)) := by
      rw [Matrix.conjTranspose_mul, hNherm, hGjherm, Matrix.mul_smul,
        Matrix.smul_mul, ← hNN]
      congr 1
      noncomm_ring
    rw [hlhs, hrhs] at hconj
    refine le_of_eq_of_le ?_ hconj
    noncomm_ring
  have hMMt0 : (0 : FullBlockMat d) ≤ M * Mᴴ := by
    refine Matrix.le_iff.mpr ?_
    rw [sub_zero]
    exact Matrix.posSemidef_self_mul_conjTranspose M
  have hMMtherm : (M * Mᴴ)ᴴ = M * Mᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hM2 : ‖M‖ ^ 2 ≤ cH * (1 + cD) ^ 2 := by
    have hnormMMt : ‖M * Mᴴ‖ ≤ cH * (1 + cD) ^ 2 := by
      have hsq : ((N * Gj * N) * (N * Gj * N))ᴴ =
          (N * Gj * N) * (N * Gj * N) := by
        rw [Matrix.conjTranspose_mul, hNGjNherm]
      have hle := norm_le_norm_of_psd_le' hMMtherm hMMt0 hMMt_le (by
        rw [Matrix.conjTranspose_smul, hsq, star_trivial])
      refine hle.trans ?_
      rw [norm_smul]
      have hprod : ‖(N * Gj * N) * (N * Gj * N)‖ ≤ (1 + cD) ^ 2 := by
        refine le_trans (norm_mul_le _ _) ?_
        rw [pow_two]
        exact mul_le_mul hNGjNnorm hNGjNnorm (norm_nonneg _)
          (by linarith only [hcD0])
      have hcHnorm : ‖cH‖ = cH := abs_of_nonneg hcH0
      rw [hcHnorm]
      exact mul_le_mul_of_nonneg_left hprod hcH0
    have e1 : ‖Mᴴ‖ * ‖Mᴴ‖ = ‖M‖ ^ 2 := by
      rw [Matrix.l2_opNorm_conjTranspose, pow_two]
    have e2 : ‖(Mᴴ)ᴴ * Mᴴ‖ = ‖Mᴴ‖ * ‖Mᴴ‖ :=
      Matrix.l2_opNorm_conjTranspose_mul_self _
    have e3 : (Mᴴ)ᴴ * Mᴴ = M * Mᴴ := by
      rw [Matrix.conjTranspose_conjTranspose]
    rw [← e1, ← e2, e3]
    exact hnormMMt
  exact hM2

private theorem normalized_sharp_gap_norm_bound
    {Gp Gj N R : FullBlockMat d} {cJ : ℝ} (hcJ0 : 0 ≤ cJ)
    (hsharpJle : fullBlockSharp Gj ≤ Gj)
    (hgapJ : Gj - fullBlockSharp Gj ≤ cJ • Gp)
    (hNherm : Nᴴ = N) (hGjherm : Gjᴴ = Gj)
    (hNGpN : N * Gp * N = 1)
    (hRdef : R = fullBlockRefl d) (hRherm : Rᴴ = R) :
    (Gj - fullBlockSharp Gj)ᴴ = Gj - fullBlockSharp Gj ∧
      ‖N * (Gj - fullBlockSharp Gj) * N‖ ≤ cJ := by
  classical
  have hgapJ0 : (0 : FullBlockMat d) ≤ Gj - fullBlockSharp Gj := by
    refine Matrix.le_iff.mpr ?_
    rw [sub_zero]
    exact Matrix.le_iff.mp hsharpJle
  have hgapJherm : (Gj - fullBlockSharp Gj)ᴴ = Gj - fullBlockSharp Gj := by
    rw [Matrix.conjTranspose_sub, hGjherm]
    congr 1
    rw [fullBlockSharp, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have hRherm' : (fullBlockRefl d)ᴴ = fullBlockRefl d := by
      rw [← hRdef]
      exact hRherm
    rw [hRherm', Matrix.conjTranspose_nonsing_inv, hGjherm]
    noncomm_ring
  have hgapN : ‖N * (Gj - fullBlockSharp Gj) * N‖ ≤ cJ := by
    have hup : N * (Gj - fullBlockSharp Gj) * N ≤
        cJ • (1 : FullBlockMat d) := by
      have h := conj_mono' hgapJ N
      rw [hNherm] at h
      refine h.trans (le_of_eq ?_)
      rw [Matrix.mul_smul, Matrix.smul_mul, hNGpN]
    have hlo : (0 : FullBlockMat d) ≤
        N * (Gj - fullBlockSharp Gj) * N := by
      have h := conj_mono' hgapJ0 N
      have h0 : N * 0 * N = (0 : FullBlockMat d) := by noncomm_ring
      rw [hNherm, h0] at h
      exact h
    refine PortableHistory.norm_le_of_sandwich (conj_herm' hNherm hgapJherm) hcJ0 hup ?_
    refine le_trans ?_ hlo
    have h1 : (0 : FullBlockMat d) ≤ cJ • (1 : FullBlockMat d) := by
      refine Matrix.le_iff.mpr ?_
      rw [sub_zero]
      exact Matrix.PosSemidef.one.smul hcJ0
    have h2 := neg_le_neg h1
    simpa only [neg_zero, neg_smul] using h2
  exact ⟨hgapJherm, hgapN⟩

private theorem normalized_dilation_difference_norm_bound [NeZero d]
    {Gp Gj N : FullBlockMat d} {cD : ℝ} (hcD0 : 0 ≤ cD)
    (horder : Gp ≤ Gj) (hdil : Gj ≤ (1 + cD) • Gp)
    (hNherm : Nᴴ = N) (hGjherm : Gjᴴ = Gj) (hGpherm : Gpᴴ = Gp)
    (hNGpN : N * Gp * N = 1) :
    ‖N * (Gj - Gp) * N‖ ≤ cD := by
  classical
  have hT3 : ‖N * (Gj - Gp) * N‖ ≤ cD := by
    have hup : Gj - Gp ≤ cD • Gp := by
      have h := sub_le_sub_right hdil Gp
      refine h.trans (le_of_eq ?_)
      rw [add_smul, one_smul, add_sub_cancel_left]
    have hupN : N * (Gj - Gp) * N ≤ cD • (1 : FullBlockMat d) := by
      have h := conj_mono' hup N
      rw [hNherm] at h
      refine h.trans (le_of_eq ?_)
      rw [Matrix.mul_smul, Matrix.smul_mul, hNGpN]
    have hloN : (0 : FullBlockMat d) ≤ N * (Gj - Gp) * N := by
      have hpsd : (0 : FullBlockMat d) ≤ Gj - Gp := by
        refine Matrix.le_iff.mpr ?_
        rw [sub_zero]
        exact Matrix.le_iff.mp horder
      have h := conj_mono' hpsd N
      have h0 : N * 0 * N = (0 : FullBlockMat d) := by
        noncomm_ring
      rw [hNherm, h0] at h
      exact h
    refine PortableHistory.norm_le_of_sandwich
      (conj_herm' hNherm (by rw [Matrix.conjTranspose_sub, hGjherm,
        hGpherm])) hcD0 hupN ?_
    refine le_trans ?_ hloN
    have h1 : (0 : FullBlockMat d) ≤ cD • (1 : FullBlockMat d) := by
      refine Matrix.le_iff.mpr ?_
      rw [sub_zero]
      exact Matrix.PosSemidef.one.smul hcD0
    have h2 := neg_le_neg h1
    simpa only [neg_zero, neg_smul] using h2
  exact hT3

/-- **The abstract pathwise variance split.** -/
theorem norm_normalized_parent_fluctuation_le [NeZero d]
    {ι : Type*} [DecidableEq ι] (Z : Finset ι) (hZne : Z.Nonempty)
    (A : ι → FullBlockMat d) (hA : ∀ i ∈ Z, (A i).PosDef)
    {Ap Gj Gp : FullBlockMat d}
    (hAp : Ap.PosDef) (hGj : Gj.PosDef) (hGp : Gp.PosDef)
    (hparentLe : Ap ≤ (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, A i)
    (hparentSharp : fullBlockSharp Ap ≤ Ap)
    (hsharpJle : fullBlockSharp Gj ≤ Gj)
    (horder : Gp ≤ Gj)
    {cH cJ cD : ℝ} (hcH0 : 0 ≤ cH) (hcJ0 : 0 ≤ cJ) (hcD0 : 0 ≤ cD)
    (hsharpPinv : (fullBlockSharp Gp)⁻¹ ≤ cH • Gp⁻¹)
    (hgapJ : Gj - fullBlockSharp Gj ≤ cJ • Gp)
    (hdil : Gj ≤ (1 + cD) • Gp) :
    ‖matSqrt Gp⁻¹ * (Ap - Gp) * matSqrt Gp⁻¹‖ ≤
      (2 + cH * (1 + cD) ^ 2) *
        ‖matSqrt Gp⁻¹ * ((Z.card : ℝ)⁻¹ • ∑ i ∈ Z, A i - Gj) *
          matSqrt Gp⁻¹‖ +
      cH * (1 + cD) ^ 2 * cJ + cD := by
  classical
  set avgA : FullBlockMat d := (Z.card : ℝ)⁻¹ • ∑ i ∈ Z, A i with havgAdef
  set R : FullBlockMat d := fullBlockRefl d with hRdef
  have hGpherm : Gpᴴ = Gp := hGp.isHermitian
  have hGjherm : Gjᴴ = Gj := hGj.isHermitian
  have hApherm : Apᴴ = Ap := hAp.isHermitian
  have hRherm : Rᴴ = R := by
    rw [hRdef, conjTranspose_eq_transpose', fullBlockRefl,
      Matrix.fromBlocks_transpose]
    simp
  -- the normalization
  set N : FullBlockMat d := matSqrt Gp⁻¹ with hNdef
  have hNherm : Nᴴ = N :=
    (matSqrt_spec hGp.inv.posSemidef).1.isHermitian
  have hNN : N * N = Gp⁻¹ := (matSqrt_spec hGp.inv.posSemidef).2
  have hNGpN : N * Gp * N = 1 := matSqrt_inv_conj hGp
  have hsqGp : matSqrt Gp * matSqrt Gp = Gp :=
    (matSqrt_spec hGp.posSemidef).2
  have hsqGpherm : (matSqrt Gp)ᴴ = matSqrt Gp :=
    (matSqrt_spec hGp.posSemidef).1.isHermitian
  have hNinv : matSqrt Gp * N = 1 := by
    rw [hNdef, matSqrt_inv hGp]
    exact Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hGp))
  have hNinv' : N * matSqrt Gp = 1 := by
    rw [hNdef, matSqrt_inv hGp]
    exact Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hGp))
  have hcard0 : (Z.card : ℝ) ≠ 0 := by
    have h := Finset.card_pos.mpr hZne
    positivity
  -- the average sandwich, rebuilt abstractly
  have hgap1 : (0 : FullBlockMat d) ≤ avgA - Ap := by
    refine Matrix.le_iff.mpr ?_
    rw [sub_zero, havgAdef]
    exact Matrix.le_iff.mp hparentLe
  have hgap2 := average_parent_gap_le_sharp_fluctuation Z hZne A hA hAp hGj
    havgAdef hparentLe hparentSharp hGjherm
  -- the burrito identity
  have hburrito := average_sharp_fluctuation_expansion (Gj := Gj) Z A hA hRdef havgAdef hcard0
  -- the three normalized terms
  have hT3 := normalized_dilation_difference_norm_bound hcD0 horder hdil
    hNherm hGjherm hGpherm hNGpN
  -- the conjugator
  set M : FullBlockMat d := N * Gj * R * matSqrt Gp with hMdef
  have hMherm : Mᴴ = matSqrt Gp * R * Gj * N := by
    rw [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hNherm, hGjherm, hRherm, hsqGpherm]
    noncomm_ring
  have hconjM : ∀ Y : FullBlockMat d,
      N * (Gj * R * Y * R * Gj) * N = M * (N * Y * N) * Mᴴ := by
    intro Y
    have h1 : M * (N * Y * N) * Mᴴ =
        N * Gj * R * ((matSqrt Gp * N) * Y * (N * matSqrt Gp)) * R *
          Gj * N := by
      rw [hMherm, hMdef]
      noncomm_ring
    rw [h1, hNinv, hNinv', Matrix.one_mul, Matrix.mul_one]
    noncomm_ring
  have hM2 := normalized_conjugator_norm_squared_bound hGp hGj hcH0 hcD0
    hsharpPinv hdil hNherm hGjherm hNGpN hNN
    hMdef hMherm hsqGp hRdef
  -- the sharp-gap term
  obtain ⟨hgapJherm, hgapN⟩ := normalized_sharp_gap_norm_bound hcJ0 hsharpJle
    hgapJ hNherm hGjherm hNGpN hRdef hRherm
  -- the T2 quantity
  set T2 : FullBlockMat d := avgA - Gj with hT2def
  have hsumherm : (∑ i ∈ Z, A i)ᴴ = ∑ i ∈ Z, A i := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i hi => (hA i hi).isHermitian
  have hT2herm : T2ᴴ = T2 := by
    rw [hT2def, Matrix.conjTranspose_sub, hGjherm, havgAdef,
      Matrix.conjTranspose_smul, star_trivial, hsumherm]
  -- the Root bound
  have hT1 : ‖N * (avgA - Ap) * N‖ ≤
      (1 + cH * (1 + cD) ^ 2) * ‖N * T2 * N‖ +
        cH * (1 + cD) ^ 2 * cJ := by
    have hT10 : (0 : FullBlockMat d) ≤ N * (avgA - Ap) * N := by
      have h := conj_mono' hgap1 N
      have h0 : N * 0 * N = (0 : FullBlockMat d) := by noncomm_ring
      rw [hNherm, h0] at h
      exact h
    have hT1herm : (N * (avgA - Ap) * N)ᴴ = N * (avgA - Ap) * N := by
      refine conj_herm' hNherm ?_
      rw [Matrix.conjTranspose_sub, hApherm, havgAdef,
        Matrix.conjTranspose_smul, star_trivial, hsumherm]
    have hT1le : N * (avgA - Ap) * N ≤
        N * (T2 + Gj * R * T2 * R * Gj +
          Gj * R * (Gj - fullBlockSharp Gj) * R * Gj) * N := by
      have hfl' : avgA - Ap ≤
          T2 + Gj * R * T2 * R * Gj +
            Gj * R * (Gj - fullBlockSharp Gj) * R * Gj := by
        refine le_of_le_of_eq hgap2 ?_
        exact hburrito
      have h := conj_mono' hfl' N
      rwa [hNherm] at h
    have hsplit : N * (T2 + Gj * R * T2 * R * Gj +
        Gj * R * (Gj - fullBlockSharp Gj) * R * Gj) * N =
        N * T2 * N + M * (N * T2 * N) * Mᴴ +
          M * (N * (Gj - fullBlockSharp Gj) * N) * Mᴴ := by
      rw [← hconjM T2, ← hconjM (Gj - fullBlockSharp Gj)]
      noncomm_ring
    have hnormle : ‖N * (avgA - Ap) * N‖ ≤
        ‖N * T2 * N + M * (N * T2 * N) * Mᴴ +
          M * (N * (Gj - fullBlockSharp Gj) * N) * Mᴴ‖ := by
      refine norm_le_norm_of_psd_le' hT1herm hT10 (by
        rw [← hsplit]; exact hT1le) ?_
      rw [← hsplit]
      refine conj_herm' hNherm ?_
      have hbursym : (Gj * R * T2 * R * Gj)ᴴ = Gj * R * T2 * R * Gj := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hGjherm, hRherm, hT2herm]
        noncomm_ring
      have hbursym2 : (Gj * R * (Gj - fullBlockSharp Gj) * R * Gj)ᴴ =
          Gj * R * (Gj - fullBlockSharp Gj) * R * Gj := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hGjherm, hRherm, hgapJherm]
        noncomm_ring
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, hT2herm,
        hbursym, hbursym2]
    refine hnormle.trans ?_
    refine le_trans (norm_add_le _ _) ?_
    have hstep1 : ‖N * T2 * N + M * (N * T2 * N) * Mᴴ‖ ≤
        ‖N * T2 * N‖ + cH * (1 + cD) ^ 2 * ‖N * T2 * N‖ := by
      refine le_trans (norm_add_le _ _) ?_
      refine add_le_add le_rfl ?_
      refine le_trans (norm_mul_le _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_left
        (Matrix.l2_opNorm_conjTranspose M).le (norm_nonneg _)) ?_
      have h := mul_le_mul (norm_mul_le M (N * T2 * N)) (le_refl ‖M‖)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      refine le_trans h ?_
      have hgoal : ‖M‖ * ‖N * T2 * N‖ * ‖M‖ =
          ‖M‖ ^ 2 * ‖N * T2 * N‖ := by ring
      rw [hgoal]
      exact mul_le_mul_of_nonneg_right hM2 (norm_nonneg _)
    have hstep2 : ‖M * (N * (Gj - fullBlockSharp Gj) * N) * Mᴴ‖ ≤
        cH * (1 + cD) ^ 2 * cJ := by
      refine le_trans (norm_mul_le _ _) ?_
      refine le_trans (mul_le_mul_of_nonneg_left
        (Matrix.l2_opNorm_conjTranspose M).le (norm_nonneg _)) ?_
      have h := mul_le_mul
        (norm_mul_le M (N * (Gj - fullBlockSharp Gj) * N)) (le_refl ‖M‖)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      refine le_trans h ?_
      have hgoal : ‖M‖ * ‖N * (Gj - fullBlockSharp Gj) * N‖ * ‖M‖ =
          ‖M‖ ^ 2 * ‖N * (Gj - fullBlockSharp Gj) * N‖ := by ring
      rw [hgoal]
      have h1 := mul_le_mul hM2 hgapN (norm_nonneg _)
        (mul_nonneg hcH0 (by positivity))
      exact h1
    calc ‖N * T2 * N + M * (N * T2 * N) * Mᴴ‖ +
        ‖M * (N * (Gj - fullBlockSharp Gj) * N) * Mᴴ‖ ≤
        (‖N * T2 * N‖ + cH * (1 + cD) ^ 2 * ‖N * T2 * N‖) +
          cH * (1 + cD) ^ 2 * cJ := add_le_add hstep1 hstep2
      _ = (1 + cH * (1 + cD) ^ 2) * ‖N * T2 * N‖ +
          cH * (1 + cD) ^ 2 * cJ := by ring
  -- assemble
  have hsplitLHS : ‖N * (Ap - Gp) * N‖ ≤
      ‖N * (avgA - Ap) * N‖ + ‖N * T2 * N‖ + ‖N * (Gj - Gp) * N‖ := by
    have hid : N * (Ap - Gp) * N =
        (-(N * (avgA - Ap) * N)) + N * T2 * N + N * (Gj - Gp) * N := by
      rw [hT2def]
      noncomm_ring
    rw [hid]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) ?_) le_rfl
    rw [norm_neg]
  calc ‖N * (Ap - Gp) * N‖ ≤
      ‖N * (avgA - Ap) * N‖ + ‖N * T2 * N‖ + ‖N * (Gj - Gp) * N‖ :=
      hsplitLHS
    _ ≤ ((1 + cH * (1 + cD) ^ 2) * ‖N * T2 * N‖ +
          cH * (1 + cD) ^ 2 * cJ) + ‖N * T2 * N‖ + cD :=
      add_le_add (add_le_add hT1 le_rfl) hT3
    _ = (2 + cH * (1 + cD) ^ 2) * ‖N * T2 * N‖ +
        cH * (1 + cD) ^ 2 * cJ + cD := by ring

end

end HCPolySupport.HighContrast.Quenched
