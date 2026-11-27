/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.NullDiscDefs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Lemma 5.3: null analytic discs

Formalization of Lemma 5.3 ("Null analytic discs") of Section 5 of the manuscript.
-/

@[expose] public section

namespace VacuumBellSeparation

noncomputable section

lemma spatialDot_eq (z w : Fin 3 → ℂ) :
    spatialDot z w = z 0 * w 0 + z 1 * w 1 + z 2 * w 2 := by
  unfold spatialDot
  rw [Fin.sum_univ_three]

lemma norm_sq_eq_re_im (x : ℂ) : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-! ### Milestone 1: a null vector orthogonal to a given vector -/

lemma exists_null_of_orth (w0 w1 w2 u0 u1 u2 : ℂ) (hu : u0 ≠ 0 ∨ u1 ≠ 0 ∨ u2 ≠ 0)
    (hwu : w0 * u0 + w1 * u1 + w2 * u2 = 0) (hww : w0 * w0 + w1 * w1 + w2 * w2 ≠ 0) :
    ∃ n0 n1 n2 : ℂ, (n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0) ∧
      w0 * n0 + w1 * n1 + w2 * n2 = 0 ∧ n0 * n0 + n1 * n1 + n2 * n2 = 0 := by
  by_cases huu : u0 * u0 + u1 * u1 + u2 * u2 = 0
  · exact ⟨u0, u1, u2, hu, hwu, huu⟩
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (w0 * w0 + w1 * w1 + w2 * w2)
    (by norm_num : 0 < 2)
  refine ⟨σ * u0 + Complex.I * (w1 * u2 - w2 * u1), σ * u1 + Complex.I * (w2 * u0 - w0 * u2),
    σ * u2 + Complex.I * (w0 * u1 - w1 * u0), ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    have key : 2 * (w0 * w0 + w1 * w1 + w2 * w2) * (u0 * u0 + u1 * u1 + u2 * u2) = 0 := by
      linear_combination (σ * u0 - Complex.I * (w1 * u2 - w2 * u1)) * h0
        + (σ * u1 - Complex.I * (w2 * u0 - w0 * u2)) * h1
        + (σ * u2 - Complex.I * (w0 * u1 - w1 * u0)) * h2
        - (u0 * u0 + u1 * u1 + u2 * u2) * hσ + (w0 * u0 + w1 * u1 + w2 * u2) * hwu
        + ((w1 * u2 - w2 * u1) * (w1 * u2 - w2 * u1) + (w2 * u0 - w0 * u2) * (w2 * u0 - w0 * u2)
          + (w0 * u1 - w1 * u0) * (w0 * u1 - w1 * u0)) * Complex.I_sq
    exact mul_ne_zero (mul_ne_zero two_ne_zero hww) huu key
  · linear_combination σ * hwu
  · linear_combination (u0 * u0 + u1 * u1 + u2 * u2) * hσ + (w0 * u0 + w1 * u1 + w2 * u2) * hwu
      + ((w1 * u2 - w2 * u1) * (w1 * u2 - w2 * u1) + (w2 * u0 - w0 * u2) * (w2 * u0 - w0 * u2)
        + (w0 * u1 - w1 * u0) * (w0 * u1 - w1 * u0)) * Complex.I_sq

lemma exists_null_scalar (w0 w1 w2 : ℂ) : ∃ n0 n1 n2 : ℂ, (n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0) ∧
    w0 * n0 + w1 * n1 + w2 * n2 = 0 ∧ n0 * n0 + n1 * n1 + n2 * n2 = 0 := by
  by_cases hww : w0 * w0 + w1 * w1 + w2 * w2 = 0
  · by_cases hw : w0 = 0 ∧ w1 = 0 ∧ w2 = 0
    · obtain ⟨h0, h1, h2⟩ := hw
      refine ⟨1, Complex.I, 0, Or.inl one_ne_zero, ?_, ?_⟩
      · simp [h0, h1, h2]
      · linear_combination Complex.I_sq
    · refine ⟨w0, w1, w2, ?_, hww, hww⟩
      by_contra hcon
      push Not at hcon
      exact hw hcon
  · by_cases h2 : w2 = 0
    · by_cases h1 : w1 = 0
      · have h0 : w0 ≠ 0 := by
          intro h0
          apply hww
          simp [h0, h1, h2]
        exact exists_null_of_orth w0 w1 w2 (-w2) 0 w0 (Or.inr (Or.inr h0)) (by ring) hww
      · exact exists_null_of_orth w0 w1 w2 w1 (-w0) 0 (Or.inl h1) (by ring) hww
    · exact exists_null_of_orth w0 w1 w2 0 w2 (-w1) (Or.inr (Or.inl h2)) (by ring) hww

/-- Milestone 1: for every `𝐰 ∈ ℂ³` there is a nonzero `𝐧` with `𝐰·𝐧 = 0` and `𝐧·𝐧 = 0`. -/
theorem exists_null_vector (w : Fin 3 → ℂ) :
    ∃ n : Fin 3 → ℂ, n ≠ 0 ∧ spatialDot w n = 0 ∧ spatialDot n n = 0 := by
  obtain ⟨n0, n1, n2, hne, hwn, hnn⟩ := exists_null_scalar (w 0) (w 1) (w 2)
  refine ⟨![n0, n1, n2], ?_, ?_, ?_⟩
  · intro hv
    have e0 : n0 = 0 := by simpa using congrFun hv 0
    have e1 : n1 = 0 := by simpa using congrFun hv 1
    have e2 : n2 = 0 := by simpa using congrFun hv 2
    rcases hne with h | h | h
    · exact h e0
    · exact h e1
    · exact h e2
  · rw [spatialDot_eq]; simpa using hwn
  · rw [spatialDot_eq]; simpa using hnn

/-! ### Milestone 2: normalization -/

/-- Milestone 2: a null vector orthogonal to `𝐰` with `|Re 𝐧| = |Im 𝐧| = 1`, `Re 𝐧 · Im 𝐧 = 0`. -/
theorem exists_normalized_null (w : Fin 3 → ℂ) :
    ∃ n : Fin 3 → ℂ, spatialDot w n = 0 ∧ spatialDot n n = 0 ∧
      (n 0).re ^ 2 + (n 1).re ^ 2 + (n 2).re ^ 2 = 1 ∧
      (n 0).im ^ 2 + (n 1).im ^ 2 + (n 2).im ^ 2 = 1 ∧
      (n 0).re * (n 0).im + (n 1).re * (n 1).im + (n 2).re * (n 2).im = 0 := by
  obtain ⟨n, hn0, hwn, hnn⟩ := exists_null_vector w
  have hnn' := hnn
  rw [spatialDot_eq, Complex.ext_iff] at hnn'
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
    Complex.zero_re, Complex.zero_im] at hnn'
  obtain ⟨hre, him⟩ := hnn'
  have hpos : 0 < (n 0).re ^ 2 + (n 1).re ^ 2 + (n 2).re ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hn0
    have hj' : 0 < Complex.normSq (n j) := Complex.normSq_pos.mpr hj
    have hsum : Complex.normSq (n j) ≤ ∑ k, Complex.normSq (n k) :=
      Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (n k)) (Finset.mem_univ j)
    rw [Fin.sum_univ_three] at hsum
    simp only [Complex.normSq_apply] at hsum hj'
    nlinarith
  obtain ⟨ρ, hρpos, hρsq⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = (n 0).re ^ 2 + (n 1).re ^ 2 + (n 2).re ^ 2 :=
    ⟨Real.sqrt _, Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩
  obtain ⟨m, hm⟩ : ∃ m : Fin 3 → ℂ, ∀ j, m j = ((ρ⁻¹ : ℝ) : ℂ) * n j :=
    ⟨fun j => ((ρ⁻¹ : ℝ) : ℂ) * n j, fun j => rfl⟩
  have hc : ρ⁻¹ ^ 2 * ((n 0).re ^ 2 + (n 1).re ^ 2 + (n 2).re ^ 2) = 1 := by
    rw [← hρsq, ← mul_pow, inv_mul_cancel₀ hρpos.ne', one_pow]
  refine ⟨m, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spatialDot_eq] at hwn ⊢
    simp only [hm]
    linear_combination ((ρ⁻¹ : ℝ) : ℂ) * hwn
  · rw [spatialDot_eq] at hnn ⊢
    simp only [hm]
    linear_combination ((ρ⁻¹ : ℝ) : ℂ) ^ 2 * hnn
  · simp only [hm, Complex.re_ofReal_mul]
    linear_combination hc
  · simp only [hm, Complex.im_ofReal_mul]
    linear_combination hc - ρ⁻¹ ^ 2 * hre
  · simp only [hm, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    linear_combination (ρ⁻¹ ^ 2 / 2) * him

/-! ### Milestone 3: estimates on the disc and the main lemma -/

lemma disc_re (a ζ m : ℂ) (E : ℝ) :
    (a + (8 * E : ℂ) * ζ * m).re = a.re + 8 * E * (ζ.re * m.re - ζ.im * m.im) := by
  have h : (8 * E : ℂ) * ζ * m = ((8 * E : ℝ) : ℂ) * (ζ * m) := by push_cast; ring
  rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.mul_re]

lemma norm_disc_sq_le (a ζ m : ℂ) (E : ℝ) (hζ : ‖ζ‖ = 1) :
    ‖a + (8 * E : ℂ) * ζ * m‖ ^ 2 ≤ 9 * ‖a‖ ^ 2 + 72 * E ^ 2 * ‖m‖ ^ 2 := by
  have hy : ‖(8 * E : ℂ) * ζ * m‖ ^ 2 = 64 * E ^ 2 * ‖m‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hζ, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, mul_one, mul_pow, mul_pow, sq_abs]
    ring
  have htri := norm_add_le a ((8 * E : ℂ) * ζ * m)
  have h0 : 0 ≤ ‖a + (8 * E : ℂ) * ζ * m‖ := norm_nonneg _
  nlinarith [sq_nonneg (8 * ‖a‖ - ‖(8 * E : ℂ) * ζ * m‖), mul_nonneg h0 (sub_nonneg.mpr htri),
    sq_nonneg (‖a‖ + ‖(8 * E : ℂ) * ζ * m‖ - ‖a + (8 * E : ℂ) * ζ * m‖)]

lemma key_real (a0 a1 a2 r0 r1 r2 E : ℝ) (hE : 0 < E) (hr : r0 ^ 2 + r1 ^ 2 + r2 ^ 2 = 1)
    (ha : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 ≤ (2 * E) ^ 2) :
    (6 * E) ^ 2 ≤ (a0 + 8 * E * r0) ^ 2 + (a1 + 8 * E * r1) ^ 2 + (a2 + 8 * E * r2) ^ 2 := by
  have hcs0 : (a0 * r0 + a1 * r1 + a2 * r2) ^ 2 ≤
      (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) * (r0 ^ 2 + r1 ^ 2 + r2 ^ 2) := by
    nlinarith [sq_nonneg (a0 * r1 - a1 * r0), sq_nonneg (a0 * r2 - a2 * r0),
      sq_nonneg (a1 * r2 - a2 * r1)]
  rw [hr, mul_one] at hcs0
  have ht : -(2 * E) ≤ a0 * r0 + a1 * r1 + a2 * r2 := by nlinarith
  have hE2 : E ^ 2 * (r0 ^ 2 + r1 ^ 2 + r2 ^ 2) = E ^ 2 := by rw [hr, mul_one]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ a0 * r0 + a1 * r1 + a2 * r2 + 2 * E by linarith)
    (show (0:ℝ) ≤ a0 * r0 + a1 * r1 + a2 * r2 + 14 * E by linarith)]

lemma scaleBy_mem_shell {μ E : ℝ} {w : ℂ × (Fin 3 → ℂ)} (hw : w ∈ complexShell μ) :
    scaleBy E w ∈ complexShell (μ / E) := by
  simp only [complexShell, Set.mem_ofPred_eq, spatialDot_eq, scaleBy] at hw ⊢
  rw [Complex.ofReal_div]
  linear_combination ((E : ℂ)⁻¹) ^ 2 * hw

lemma euclidSq_scaleBy (E : ℝ) (w : ℂ × (Fin 3 → ℂ)) :
    euclidSq (scaleBy E w) = euclidSq w / E ^ 2 := by
  simp only [euclidSq, scaleBy, Fin.sum_univ_three, norm_div, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]
  ring

lemma reLorentzSq_scaleBy (E : ℝ) (w : ℂ × (Fin 3 → ℂ)) :
    reLorentzSq (scaleBy E w) = reLorentzSq w / E ^ 2 := by
  simp only [reLorentzSq, reSpatialSq, scaleBy, Fin.sum_univ_three, Complex.div_ofReal_re,
    div_pow]
  ring

lemma abs_le_two_mul_of_sq_le {x E : ℝ} (hE : 0 < E) (h : x ^ 2 ≤ (2 * E) ^ 2) :
    |x| ≤ 2 * E := by
  rw [abs_le]
  constructor <;> nlinarith

/-- **Lemma 5.3 (null analytic discs).** -/
theorem exists_null_disc {μ En : ℝ} (hμ : 0 < μ) (hE : μ ≤ En)
    {z : ℂ × (Fin 3 → ℂ)} (hz : z ∈ complexShell μ) (hzn : euclidSq z ≤ (2 * En) ^ 2) :
    ∃ n : Fin 3 → ℂ,
      nullDisc z En n 0 = z ∧
      (∀ ζ : ℂ, nullDisc z En n ζ ∈ complexShell μ) ∧
      (∀ ζ : ℂ, ‖ζ‖ = 1 →
        (6 * En) ^ 2 ≤ reSpatialSq (nullDisc z En n ζ).2 ∧
        |(nullDisc z En n ζ).1.re| ≤ 2 * En ∧
        reLorentzSq (nullDisc z En n ζ) ≤ -32 * En ^ 2 ∧
        euclidSq (nullDisc z En n ζ) < (14 * En) ^ 2 ∧
        (μ / En, scaleBy En (nullDisc z En n ζ)) ∈ normalizedTarget) := by
  have hEpos : 0 < En := lt_of_lt_of_le hμ hE
  obtain ⟨n, hwn, hnn, hre1, him1, hcross⟩ := exists_normalized_null z.2
  have hzn' : ‖z.1‖ ^ 2 + (‖z.2 0‖ ^ 2 + ‖z.2 1‖ ^ 2 + ‖z.2 2‖ ^ 2) ≤ (2 * En) ^ 2 := by
    have h := hzn
    unfold euclidSq at h
    rwa [Fin.sum_univ_three] at h
  have hshell : ∀ ζ : ℂ, nullDisc z En n ζ ∈ complexShell μ := by
    intro ζ
    have hz' := hz
    simp only [complexShell, Set.mem_ofPred_eq, spatialDot_eq] at hz' ⊢
    rw [spatialDot_eq] at hwn hnn
    simp only [nullDisc]
    linear_combination hz' - (16 * (En : ℂ) * ζ) * hwn - (64 * (En : ℂ) ^ 2 * ζ ^ 2) * hnn
  refine ⟨n, ?_, hshell, ?_⟩
  · change (z.1, fun j => z.2 j + (8 * En : ℂ) * 0 * n j) = z
    have h0 : (fun j => z.2 j + (8 * En : ℂ) * 0 * n j) = z.2 := by
      funext j
      simp
    exact Prod.ext_iff.mpr ⟨rfl, h0⟩
  · intro ζ hζ
    have hcs : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
      have h := norm_sq_eq_re_im ζ
      rw [hζ] at h
      linarith
    have h1 : (nullDisc z En n ζ).1 = z.1 := rfl
    have hz1 : z.1.re ^ 2 ≤ (2 * En) ^ 2 := by
      linarith [norm_sq_eq_re_im z.1, sq_nonneg z.1.im, sq_nonneg ‖z.2 0‖, sq_nonneg ‖z.2 1‖,
        sq_nonneg ‖z.2 2‖]
    have hR : reSpatialSq (nullDisc z En n ζ).2 =
        ((z.2 0).re + 8 * En * (ζ.re * (n 0).re - ζ.im * (n 0).im)) ^ 2 +
        ((z.2 1).re + 8 * En * (ζ.re * (n 1).re - ζ.im * (n 1).im)) ^ 2 +
        ((z.2 2).re + 8 * En * (ζ.re * (n 2).re - ζ.im * (n 2).im)) ^ 2 := by
      simp only [reSpatialSq, nullDisc, Fin.sum_univ_three, disc_re]
    have hr : (ζ.re * (n 0).re - ζ.im * (n 0).im) ^ 2 + (ζ.re * (n 1).re - ζ.im * (n 1).im) ^ 2
        + (ζ.re * (n 2).re - ζ.im * (n 2).im) ^ 2 = 1 := by
      linear_combination ζ.re ^ 2 * hre1 + ζ.im ^ 2 * him1 - 2 * ζ.re * ζ.im * hcross + hcs
    have ha : (z.2 0).re ^ 2 + (z.2 1).re ^ 2 + (z.2 2).re ^ 2 ≤ (2 * En) ^ 2 := by
      linarith [norm_sq_eq_re_im (z.2 0), norm_sq_eq_re_im (z.2 1), norm_sq_eq_re_im (z.2 2),
        sq_nonneg (z.2 0).im, sq_nonneg (z.2 1).im, sq_nonneg (z.2 2).im, sq_nonneg ‖z.1‖]
    have hS : (6 * En) ^ 2 ≤ reSpatialSq (nullDisc z En n ζ).2 := by
      rw [hR]
      exact key_real _ _ _ _ _ _ En hEpos hr ha
    have hL : reLorentzSq (nullDisc z En n ζ) ≤ -32 * En ^ 2 := by
      unfold reLorentzSq
      rw [h1]
      linarith [hS, hz1]
    have hEu : euclidSq (nullDisc z En n ζ) < (14 * En) ^ 2 := by
      have e0 := norm_disc_sq_le (z.2 0) ζ (n 0) En hζ
      have e1 := norm_disc_sq_le (z.2 1) ζ (n 1) En hζ
      have e2 := norm_disc_sq_le (z.2 2) ζ (n 2) En hζ
      have hnorm : ‖n 0‖ ^ 2 + ‖n 1‖ ^ 2 + ‖n 2‖ ^ 2 = 2 := by
        linear_combination norm_sq_eq_re_im (n 0) + norm_sq_eq_re_im (n 1) +
          norm_sq_eq_re_im (n 2) + hre1 + him1
      have hnorm' : En ^ 2 * ‖n 0‖ ^ 2 + En ^ 2 * ‖n 1‖ ^ 2 + En ^ 2 * ‖n 2‖ ^ 2 = 2 * En ^ 2 := by
        linear_combination En ^ 2 * hnorm
      have hE2 : 0 < En ^ 2 := pow_pos hEpos 2
      simp only [euclidSq, nullDisc, Fin.sum_univ_three]
      linarith [e0, e1, e2, hnorm', hzn', sq_nonneg ‖z.1‖, hE2]
    refine ⟨hS, ?_, hL, hEu, ?_⟩
    · rw [h1]
      exact abs_le_two_mul_of_sq_le hEpos hz1
    · simp only [normalizedTarget, Set.mem_ofPred_eq]
      refine ⟨div_nonneg hμ.le hEpos.le, (div_le_one₀ hEpos).mpr hE, scaleBy_mem_shell (hshell ζ),
        ?_, ?_⟩
      · rw [euclidSq_scaleBy, div_le_iff₀ (pow_pos hEpos 2)]
        linarith [hEu, sq_nonneg En]
      · rw [reLorentzSq_scaleBy, div_le_iff₀ (pow_pos hEpos 2)]
        linarith [hL, sq_nonneg En]

end

end VacuumBellSeparation
