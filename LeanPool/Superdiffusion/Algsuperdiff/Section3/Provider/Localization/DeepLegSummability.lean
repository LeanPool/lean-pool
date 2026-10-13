/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Localization.LocalizationAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Base.AnnealedPlateau

/-!
# DeepLegSummability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section3.Provider.Localization

open _root_.MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The shell-index monotonicity of the cutoff's ellipticity witness -/

/-- **The cutoff local control is monotone in the shell index.**  Lowering the
shell index deletes the leading terms of a nonnegative convergent series.

This is *not*
`Provider.Diffusivity.ApproximateRecurrence.Closure.cutoffLocalControl_mono`,
which is monotonicity in the scale `ell` at a fixed shell index and is proved
termwise from `localCubeControl_mono`; this one moves the other argument and is
a tail-truncation statement.  The name is deliberately different so that a
consumer may open both. -/
theorem cutoffLocalControl_mono_shell (ell : ℤ) {k m : ℤ} (hkm : k ≤ m)
    (omega : CutoffSample d) :
    cutoffLocalControl ell k omega ≤ cutoffLocalControl ell m omega := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = m - (t : ℤ) := ⟨(m - k).toNat, by omega⟩
  have hf : Summable (fun r : ℕ => localCubeControl ell (omega.1 (m - (r : ℤ)))) :=
    summable_cutoffLocalControl ell m omega
  have hsplit := hf.sum_add_tsum_nat_add t
  have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range t, localCubeControl ell (omega.1 (m - (i : ℤ))) :=
    Finset.sum_nonneg fun i _ => localCubeControl_nonneg _ _
  have heq : cutoffLocalControl ell (m - (t : ℤ)) omega =
      ∑' i : ℕ, localCubeControl ell (omega.1 (m - ((i + t : ℕ) : ℤ))) := by
    unfold cutoffLocalControl
    refine tsum_congr fun i => ?_
    have hidx : m - (t : ℤ) - (i : ℤ) = m - ((i + t : ℕ) : ℤ) := by push_cast; ring
    rw [hidx]
  have hm : cutoffLocalControl ell m omega =
      ∑' r : ℕ, localCubeControl ell (omega.1 (m - (r : ℤ))) := rfl
  rw [heq, hm, ← hsplit]
  linarith

/-- The cutoff's entry envelope on a cube is nonnegative. -/
theorem coefficientCutoffCubeEntryBound_nonneg (M : ABKModel d) (k : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    0 ≤ coefficientCutoffCubeEntryBound M k omega Q := by
  unfold coefficientCutoffCubeEntryBound
  exact add_nonneg M.nu_pos.le (cutoffLocalControl_nonneg _ _ _)

/-- The cutoff's entry envelope on a cube is monotone in the shell index. -/
theorem coefficientCutoffCubeEntryBound_mono (M : ABKModel d) {k m : ℤ} (hkm : k ≤ m)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    coefficientCutoffCubeEntryBound M k omega Q ≤
      coefficientCutoffCubeEntryBound M m omega Q := by
  unfold coefficientCutoffCubeEntryBound
  have := cutoffLocalControl_mono_shell (cubeOriginCoverScale Q) hkm omega
  linarith

/-- **The cutoff's upper ellipticity constant is monotone in the shell index.**
This is the moving comparator's only `j`-dependence inside
`Ch02.normalizedBlockResponseUniformBound`; the lower constant is the constant
`M.nu`. -/
theorem coefficientCutoffCubeEllipticityUpper_mono (M : ABKModel d) {k m : ℤ}
    (hkm : k ≤ m) (omega : CutoffSample d) (Q : TriadicCube d) :
    coefficientCutoffCubeEllipticityUpper M k omega Q ≤
      coefficientCutoffCubeEllipticityUpper M m omega Q := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hb := coefficientCutoffCubeEntryBound_mono M hkm omega Q
  have hb0 := coefficientCutoffCubeEntryBound_nonneg M k omega Q
  unfold coefficientCutoffCubeEllipticityUpper
  exact div_le_div_of_nonneg_right
    (add_le_add_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb 2)
        (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg d)))
      (M.nu ^ 2))
    hnu.le

/-! ## The isotropic normalizer's row bound -/

/-- The row-absolute-square bound of a diagonal full block matrix. -/
theorem fullBlockMatRowAbsSqBound_diagonal (v : BlockCoord d → ℝ) :
    fullBlockMatRowAbsSqBound (Matrix.diagonal v) = ∑ i, (v i) ^ 2 := by
  unfold fullBlockMatRowAbsSqBound
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (∑ j, |Matrix.diagonal v i j|) = |v i| := by
    simp [Matrix.diagonal_apply, apply_ite abs]
  rw [h, sq_abs]

/-- **The square-root normalizer of the isotropic comparator.**  At
`a0 = sigma * 1` the Chapter 2 normalizer is the diagonal gauge
`diag(sigma^{1/2}, sigma^{-1/2})`, whose row bound is `d (sigma + sigma^{-1})`. -/
theorem fullBlockMatRowAbsSqBound_constantFullBlockMatrixSqrt_isotropic [NeZero d]
    (sigma : Observable.PositiveScalar) :
    fullBlockMatRowAbsSqBound (Ch02.constantFullBlockMatrixSqrt
        (Observable.isotropicComparatorMatrix (d := d) sigma)) =
      (d : ℝ) * ((sigma : ℝ) + (sigma : ℝ)⁻¹) := by
  have hsig : (0 : ℝ) < (sigma : ℝ) := sigma.property
  have hrw : Ch02.constantFullBlockMatrixSqrt
      (Observable.isotropicComparatorMatrix (d := d) sigma) =
      Matrix.diagonal (Ch05.Section56.scalarFullBlockSqrtDiag (d := d)
        (sigma : ℝ) (sigma : ℝ)) := by
    change Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) (sigma : ℝ)) = _
    exact Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt hsig
  rw [hrw, fullBlockMatRowAbsSqBound_diagonal, Fintype.sum_sum_type]
  simp only [Ch05.Section56.scalarFullBlockSqrtDiag, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sq_sqrt hsig.le, ← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.2 hsig.le)]
  ring

/-- **The inverse square-root normalizer of the isotropic comparator.**  Its row
bound is the same `d (sigma + sigma^{-1})`. -/
theorem fullBlockMatRowAbsSqBound_constantFullBlockMatrixInvSqrt_isotropic [NeZero d]
    (sigma : Observable.PositiveScalar) :
    fullBlockMatRowAbsSqBound (Ch02.constantFullBlockMatrixInvSqrt
        (Observable.isotropicComparatorMatrix (d := d) sigma)) =
      (d : ℝ) * ((sigma : ℝ) + (sigma : ℝ)⁻¹) := by
  have hsig : (0 : ℝ) < (sigma : ℝ) := sigma.property
  have hrw : Ch02.constantFullBlockMatrixInvSqrt
      (Observable.isotropicComparatorMatrix (d := d) sigma) =
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d)
        (sigma : ℝ) (sigma : ℝ)) := by
    change Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) (sigma : ℝ)) = _
    exact Ch05.Section57.constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt hsig
  rw [hrw, fullBlockMatRowAbsSqBound_diagonal, Fintype.sum_sum_type]
  simp only [Ch04.scalarFullBlockInvSqrtDiag, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sq_sqrt hsig.le, ← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.2 hsig.le)]
  ring

/-! ## The plateau ceiling, uniform below a scale -/

/-- **The annealed plateau, read uniformly below a scale.**  The upper plateau
bound of `Provider.Base.annealedPlateau` is increasing in the scale, so its
value at `m` bounds `sigmaBar_k` for every `k <= m`.

The ceiling is spelled with the constant
`Provider.Base.cutoffPlateauAmplitude`, whose
body is definitionally the plateau amplitude `annealedPlateau` displays: no
statement in this module spells that product by hand.  The two side conditions
after the unfold (`hpow`, `hcoef`) are what the monotonicity step needs and are
not a re-spelling of the ceiling. -/
theorem sigmaBar_le_plateauCeiling (M : ABKModel d) {k m : ℤ} (hkm : k ≤ m) :
    (Annealed.sigmaBar M k : ℝ) ≤
      M.nu * (1 + Provider.Base.cutoffPlateauAmplitude M m) := by
  refine (Provider.Base.annealedPlateau M k).2.trans ?_
  rw [Provider.Base.cutoffPlateauAmplitude]
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hc : (0 : ℝ) < Disorder.cstarPlus M := Disorder.cstarPlus_pos M
  have hpow : (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) ≤ (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hkm' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    exact mul_le_mul_of_nonneg_left hkm' (by positivity)
  have hcoef : (0 : ℝ) ≤ Disorder.cstarPlus M * (2 * M.nu ^ 2)⁻¹ * M.gamma⁻¹ *
      (1 + 4 * M.gamma) :=
    mul_nonneg (mul_nonneg (mul_nonneg hc.le (by positivity)) (by positivity)) (by linarith)
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_left hpow hcoef) 1) hnu.le

/-! ## The uniform bound at the moving comparator -/

/-- The explicit form of CoarseGraining's uniform descendant bound: it is a
`let`-free restatement of `Ch02.normalizedBlockResponseUniformBound`. -/
theorem normalizedBlockResponseUniformBound_eq [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) :
    Ch02.normalizedBlockResponseUniformBound Q a a0 =
      ((a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2))⁻¹ *
          fullBlockMatRowAbsSqBound (Ch02.constantFullBlockMatrixSqrt a0) +
        ((a.coeffOn Q).lam / (1 + 2 * (a.coeffOn Q).Lam ^ 2))⁻¹ *
          blockMatrixOfCoeffNormSqBound (a.coeffOn Q).lam (a.coeffOn Q).Lam *
          fullBlockMatRowAbsSqBound (Ch02.constantFullBlockMatrixInvSqrt a0) := rfl

private theorem coefficientCutoff_coeffOn_lam (M : ABKModel d) (k : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    ((coefficientCutoffTriadicCoeffFamily M k omega).coeffOn Q).lam = M.nu := rfl

private theorem coefficientCutoff_coeffOn_Lam (M : ABKModel d) (k : ℤ)
    (omega : CutoffSample d) (Q : TriadicCube d) :
    ((coefficientCutoffTriadicCoeffFamily M k omega).coeffOn Q).Lam =
      coefficientCutoffCubeEllipticityUpper M k omega Q := rfl

private theorem blockMatrixOfCoeffNormSqBound_nonneg (lam L : ℝ) :
    0 ≤ blockMatrixOfCoeffNormSqBound lam L := by
  unfold blockMatrixOfCoeffNormSqBound
  have : (0 : ℝ) ≤ lam⁻¹ * lam⁻¹ := mul_self_nonneg _
  positivity

private theorem blockMatrixOfCoeffNormSqBound_mono {lam L L' : ℝ} (hL : 0 ≤ L)
    (hLL' : L ≤ L') : blockMatrixOfCoeffNormSqBound lam L ≤
      blockMatrixOfCoeffNormSqBound lam L' := by
  unfold blockMatrixOfCoeffNormSqBound
  have hinv : (0 : ℝ) ≤ lam⁻¹ * lam⁻¹ := mul_self_nonneg _
  have hsq : L ^ 2 ≤ L' ^ 2 := pow_le_pow_left₀ hL hLL' 2
  have hlin : 2 * (2 * L ^ 2 + 1) ≤ 2 * (2 * L' ^ 2 + 1) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left hsq (by norm_num)) 1)
      (by norm_num)
  exact add_le_add (mul_le_mul_of_nonneg_left hsq (by norm_num))
    (mul_le_mul (mul_le_mul_of_nonneg_right hlin hinv) (add_le_add_left hsq 1)
      (by positivity) (mul_nonneg (by positivity) hinv))

/-- **The uniform descendant bound at the moving comparator.**  CoarseGraining's
`Ch02.normalizedBlockResponseUniformBound` at the cutoff family of shell index
`k` and the isotropic comparator `sigmaBar_k` is bounded by an explicit
expression in any upper bound `L` for the cutoff's cube ellipticity constant
and any upper bound `T` for `sigmaBar_k + sigmaBar_k⁻¹`. -/
theorem normalizedBlockResponseUniformBound_coefficientCutoff_isotropic_le [NeZero d]
    (M : ABKModel d) (Q : TriadicCube d) (omega : CutoffSample d) (k : ℤ) {L T : ℝ}
    (hL : coefficientCutoffCubeEllipticityUpper M k omega Q ≤ L)
    (hT : (Annealed.sigmaBar M k : ℝ) + ((Annealed.sigmaBar M k : ℝ))⁻¹ ≤ T) :
    Ch02.normalizedBlockResponseUniformBound Q
        (coefficientCutoffTriadicCoeffFamily M k omega)
        (Observable.isotropicComparatorMatrix (Annealed.sigmaBar M k)) ≤
      (1 + 2 * L ^ 2) / M.nu * (1 + blockMatrixOfCoeffNormSqBound M.nu L) *
        ((d : ℝ) * T) := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M k : ℝ) := (Annealed.sigmaBar M k).property
  have hLk0 : (0 : ℝ) ≤ coefficientCutoffCubeEllipticityUpper M k omega Q :=
    hnu.le.trans (coefficientCutoffCoeffOn M k omega Q).lam_le_Lam
  have hL0 : (0 : ℝ) ≤ L := hLk0.trans hL
  have hA0 : (0 : ℝ) ≤ (d : ℝ) * ((Annealed.sigmaBar M k : ℝ) +
      ((Annealed.sigmaBar M k : ℝ))⁻¹) := by positivity
  have hAm : (d : ℝ) * ((Annealed.sigmaBar M k : ℝ) + ((Annealed.sigmaBar M k : ℝ))⁻¹) ≤
      (d : ℝ) * T := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact mul_le_mul_of_nonneg_left hT hd
  have hcm : (1 + 2 * coefficientCutoffCubeEllipticityUpper M k omega Q ^ 2) / M.nu ≤
      (1 + 2 * L ^ 2) / M.nu :=
    div_le_div_of_nonneg_right
      (add_le_add_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLk0 hL 2) (by norm_num)) 1)
      hnu.le
  have hcL0 : (0 : ℝ) ≤ (1 + 2 * L ^ 2) / M.nu := by positivity
  have hGm := blockMatrixOfCoeffNormSqBound_mono (lam := M.nu) hLk0 hL
  have hG0 := blockMatrixOfCoeffNormSqBound_nonneg M.nu
    (coefficientCutoffCubeEllipticityUpper M k omega Q)
  have hGL0 := blockMatrixOfCoeffNormSqBound_nonneg M.nu L
  rw [normalizedBlockResponseUniformBound_eq, coefficientCutoff_coeffOn_lam,
    coefficientCutoff_coeffOn_Lam,
    fullBlockMatRowAbsSqBound_constantFullBlockMatrixSqrt_isotropic,
    fullBlockMatRowAbsSqBound_constantFullBlockMatrixInvSqrt_isotropic, inv_div]
  calc
    (1 + 2 * coefficientCutoffCubeEllipticityUpper M k omega Q ^ 2) / M.nu *
          ((d : ℝ) * ((Annealed.sigmaBar M k : ℝ) + ((Annealed.sigmaBar M k : ℝ))⁻¹)) +
        (1 + 2 * coefficientCutoffCubeEllipticityUpper M k omega Q ^ 2) / M.nu *
            blockMatrixOfCoeffNormSqBound M.nu
              (coefficientCutoffCubeEllipticityUpper M k omega Q) *
          ((d : ℝ) * ((Annealed.sigmaBar M k : ℝ) + ((Annealed.sigmaBar M k : ℝ))⁻¹)) ≤
        (1 + 2 * L ^ 2) / M.nu * ((d : ℝ) * T) +
          (1 + 2 * L ^ 2) / M.nu * blockMatrixOfCoeffNormSqBound M.nu L * ((d : ℝ) * T) := by
      refine add_le_add (mul_le_mul hcm hAm hA0 hcL0) ?_
      exact mul_le_mul (mul_le_mul hcm hGm hG0 hcL0) hAm hA0 (mul_nonneg hcL0 hGL0)
    _ = (1 + 2 * L ^ 2) / M.nu * (1 + blockMatrixOfCoeffNormSqBound M.nu L) *
          ((d : ℝ) * T) := by ring

/-- ** The uniform-in-`j` pathwise leg bound at the moving comparator.**  For every
sample and every scale `m` and gap `h`, one constant bounds both breakdown legs
of every descendant of `□_m`, at the MOVING comparator `(a_{m-j-h},
sigmaBar_{m-j-h})`, uniformly in the depth `j`.

It is entirely deterministic: CoarseGraining's uniform descendant bound is
universally quantified in `(a, a0)`, and the `j`-dependence of its explicit
value is controlled by the shell monotonicity of the cutoff's ellipticity
constant and by the annealed plateau. -/
theorem exists_uniform_bound_deep_breakdownLeg [NeZero d] (M : ABKModel d) (m : ℤ)
    (hgap : ℕ) (omega : CutoffSample d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ,
      ∀ R ∈ descendantsAtScale (originCube d m) (m - (j : ℤ)),
        breakdownLegA R
              (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
              (Observable.isotropicComparatorMatrix
                (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) ≤ D ∧
          breakdownLegB R
              (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
              (Observable.isotropicComparatorMatrix
                (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) ≤ D := by
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  set L : ℝ := coefficientCutoffCubeEllipticityUpper M m omega (originCube d m) with hLdef
  set T : ℝ := M.nu * (1 + Provider.Base.cutoffPlateauAmplitude M m) + M.nu⁻¹ with hTdef
  have hL0 : (0 : ℝ) ≤ L := by
    rw [hLdef]
    exact hnu.le.trans (coefficientCutoffCoeffOn M m omega (originCube d m)).lam_le_Lam
  have hT0 : (0 : ℝ) ≤ T := by
    have hamp : (0 : ℝ) < Provider.Base.cutoffPlateauAmplitude M m :=
      Provider.Base.cutoffPlateauAmplitude_pos M m
    have hinv : (0 : ℝ) ≤ M.nu⁻¹ := inv_nonneg.2 hnu.le
    have hmain : (0 : ℝ) ≤ M.nu * (1 + Provider.Base.cutoffPlateauAmplitude M m) :=
      mul_nonneg hnu.le (by linarith)
    rw [hTdef]
    linarith
  refine ⟨2 * ((1 + 2 * L ^ 2) / M.nu * (1 + blockMatrixOfCoeffNormSqBound M.nu L) *
    ((d : ℝ) * T)), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (1 + 2 * L ^ 2) / M.nu := by positivity
    have h2 : (0 : ℝ) ≤ 1 + blockMatrixOfCoeffNormSqBound M.nu L := by
      have := blockMatrixOfCoeffNormSqBound_nonneg M.nu L
      linarith
    have h3 : (0 : ℝ) ≤ (d : ℝ) * T := mul_nonneg (Nat.cast_nonneg d) hT0
    have := mul_nonneg (mul_nonneg h1 h2) h3
    linarith
  · intro j R hR
    have hk : m - (j : ℤ) - (hgap : ℤ) ≤ m := by omega
    have hsig : (0 : ℝ) < (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)) : ℝ) :=
      (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ))).property
    have hL : coefficientCutoffCubeEllipticityUpper M (m - (j : ℤ) - (hgap : ℤ)) omega
        (originCube d m) ≤ L :=
      coefficientCutoffCubeEllipticityUpper_mono M hk omega (originCube d m)
    have hlow : M.nu ≤ (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)) : ℝ) :=
      (Provider.Base.annealedPlateau M (m - (j : ℤ) - (hgap : ℤ))).1
    have hinvle : ((Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)) : ℝ))⁻¹ ≤ M.nu⁻¹ := by
      exact inv_anti₀ hnu hlow
    have hT : (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)) : ℝ) +
        ((Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)) : ℝ))⁻¹ ≤ T := by
      have hup := sigmaBar_le_plateauCeiling M hk
      rw [hTdef]
      linarith
    have hbound := normalizedBlockResponseUniformBound_coefficientCutoff_isotropic_le
      M (originCube d m) omega (m - (j : ℤ) - (hgap : ℤ)) hL hT
    have hmax := Ch02.normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
      (a := coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
      (Q := originCube d m) (R := R) (k := m - (j : ℤ))
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) hR
    constructor
    · have hA := breakdownLegA_le_two_mul_normalizedBlockResponseMax
        (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
        (Observable.isotropicComparatorMatrix
          (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) hR
      linarith
    · have hB := breakdownLegB_le_two_mul_normalizedBlockResponseMax
        (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
        (Observable.isotropicComparatorMatrix
          (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))) hR
      linarith

/-! ## (b) The two deep summability discharges -/

/-- **The deep `a`-leg scale series is summable, pathwise.**  This is the first
`Summable` premise of `localization_mathcalE_estimate_ae`, at its exact
carriers. -/
theorem summable_deep_breakdownLegA_scale_series [NeZero d] (M : ABKModel d) (m : ℤ)
    (hgap : ℕ) {s : ℝ} (hs : 0 < s) (omega : CutoffSample d) :
    Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => breakdownLegA R
          (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) := by
  obtain ⟨D, hD0, hD⟩ := exists_uniform_bound_deep_breakdownLeg M m hgap omega
  exact summable_gridScaleSeries_terms (leg := fun j R => breakdownLegA R
      (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ))))) m hs hD0
    (fun _ R _ => breakdownLegA_nonneg R _ _) (fun j R hR => (hD j R hR).1)

/-- **The deep `a^t`-leg scale series is summable, pathwise.**  This is the
second `Summable` premise of `localization_mathcalE_estimate_ae`, at its exact
carriers. -/
theorem summable_deep_breakdownLegB_scale_series [NeZero d] (M : ABKModel d) (m : ℤ)
    (hgap : ℕ) {s : ℝ} (hs : 0 < s) (omega : CutoffSample d) :
    Summable (fun j : ℕ => Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
      legScaleAverage (originCube d m) (m - (j : ℤ)) s
        (fun R => breakdownLegB R
          (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
          (Observable.isotropicComparatorMatrix
            (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) := by
  obtain ⟨D, hD0, hD⟩ := exists_uniform_bound_deep_breakdownLeg M m hgap omega
  exact summable_gridScaleSeries_terms (leg := fun j R => breakdownLegB R
      (coefficientCutoffTriadicCoeffFamily M (m - (j : ℤ) - (hgap : ℤ)) omega)
      (Observable.isotropicComparatorMatrix
        (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ))))) m hs hD0
    (fun _ R _ => breakdownLegB_nonneg R _ _) (fun j R hR => (hD j R hR).2)

/-! ## (c) The endpoint, unconditional -/

/-- **(c) `l.localization.mathcalE`, with both deep `Summable` premises
discharged.**  This is `localization_mathcalE_estimate_ae` with its TWO
conditional-A premises removed; every hypothesis that remains is a source
binder of the printed lemma or the parametric good-event constant `Ccg`.  The
five-term display, the null-set placement and every constant are character
identical to the proved endpoint's; nothing here re-proves the analysis. -/
theorem localization_mathcalE_estimate_ae_unconditional (d : ℕ) [NeZero d] :
    ∃ Cs Cg Ci : ℝ, 0 < Cs ∧ 0 < Cg ∧ 0 < Ci ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        mStarStar M < m0 →
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        Cs * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Cg * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        Ci * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        ∀ (Ccg : ℝ), 0 < Ccg →
          ∀ (m : ℤ), m ≤ m0 →
            ∀ (hgap : ℕ), M.gamma * (hgap : ℝ) ≤ 1 →
              ∀ (s : ℝ) (hs8 : 8 * M.gamma ≤ s), s ≤ 1 →
                ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
                  Observable.cutoffHomogenizationError M m
                        ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8)
                          M.shellPrefix.gamma_pos).trans_le hs8⟩ omega ^ 2 ≤
                    12 * (Ch02.geometricDiscount s 2 *
                        gridScaleSeries m s (fun j R => breakdownLegA R
                          (coefficientCutoffTriadicCoeffFamily M
                            (m - (j : ℤ) - (hgap : ℤ)) omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) +
                      12 * (Ch02.geometricDiscount s 2 *
                        gridScaleSeries m s (fun j R => breakdownLegB R
                          (coefficientCutoffTriadicCoeffFamily M
                            (m - (j : ℤ) - (hgap : ℤ)) omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M (m - (j : ℤ) - (hgap : ℤ)))))) +
                      4 * (8 * (324 * responseSensitivityConst d *
                          (16 * Ccg + 8 * Ccg ^ 2) *
                          ((Disorder.cstar M)⁻¹ * M.gamma))) *
                        MultiscaleEstimate.waveSizesTotalW2 M m hgap s omega.1 +
                      8 * (⨆ j : ℕ, Real.rpow (3 : ℝ) (-(s / 4) * 2 * (j : ℝ)) *
                          badGridAverage M Ccg m hgap s j omega) *
                        (Ch02.HomogenizationErrorOnCube (originCube d m) (s / 4)
                          Ch02.MultiscaleExponent.infinity
                          (Ch02.MultiscaleExponent.finite 2)
                          (coefficientCutoffTriadicCoeffFamily M m omega)
                          (Observable.isotropicComparatorMatrix
                            (Annealed.sigmaBar M m))) ^ 2 +
                      1024 * (Cs * (48 * Ccg)) * M.gamma ^ 2 *
                        ((hgap : ℝ) ^ 2 + (s ^ 2)⁻¹ +
                          (E : ℝ) ^ 4 * |Real.log M.gamma| ^ 4) := by
  obtain ⟨Cs, Cg, Ci, hCs, hCg, hCi, hmain⟩ := localization_mathcalE_estimate_ae d
  refine ⟨Cs, Cg, Ci, hCs, hCg, hCi, ?_⟩
  intro M m0 E hm0 hstate hCEs hCEg hCEi hgammaE Ccg hCcg m hmm0 hgap hgh s hs8 hs1
  have hs : (0 : ℝ) < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs8
  filter_upwards [hmain M m0 E hm0 hstate hCEs hCEg hCEi hgammaE Ccg hCcg m hmm0 hgap hgh
    s hs8 hs1] with omega homega
  exact homega (summable_deep_breakdownLegA_scale_series M m hgap hs omega)
    (summable_deep_breakdownLegB_scale_series M m hgap hs omega)

end

end Algsuperdiff.Section3.Provider.Localization
