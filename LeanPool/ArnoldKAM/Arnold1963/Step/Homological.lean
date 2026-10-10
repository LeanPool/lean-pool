/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Step.FourierDifferential

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set Complex
open scoped NNReal
namespace KamProject.Arnold1963

/-- The coefficient solving the homological equation for one nonzero Fourier mode. -/
def homologicalCoeff {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (ω : ComplexSpace n → ComplexSpace n)
    (p : ComplexSpace n) (k : FourierIndex n) : ℂ :=
  I * f.fourierCoeff p k / indexPairing k (ω p)

/-- The finite Fourier generating function solving the truncated homological equation. -/
def homologicalGenerator {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (f : AnalyticPhaseFunction n G ρ) (ω : ComplexSpace n → ComplexSpace n)
    (N : ℝ) (z : ComplexPhaseSpace n) : ℂ :=
  ∑ k ∈ lowModes n N, homologicalCoeff f ω z.1 k * fourierMonomial k z.2

variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
  (f : AnalyticPhaseFunction n G ρ) {ω : ComplexSpace n → ComplexSpace n} {K N : ℝ}

theorem analyticAt_homologicalCoeff {p : ComplexSpace n} (hp : p ∈ G)
    (hω : AnalyticAt ℂ ω p) (hK : 0 < K) (hnr : FiniteNonresonant (ω p) K N)
    {k : FourierIndex n} (hk : k ∈ lowModes n N) :
    AnalyticAt ℂ (fun P => homologicalCoeff f ω P k) p :=
  (analyticAt_const.mul (f.analyticOnNhd_fourierCoeff k p hp)).div
    ((analyticAt_indexPairing k _).comp hω) (hnr.ne_zero hK hk)

theorem analyticAt_homologicalGenerator {z : ComplexPhaseSpace n} (hz : z.1 ∈ G)
    (hω : AnalyticAt ℂ ω z.1) (hK : 0 < K) (hnr : FiniteNonresonant (ω z.1) K N) :
    AnalyticAt ℂ (homologicalGenerator f ω N) z := by
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact ((analyticAt_homologicalCoeff f hz hω hK hnr hk).comp
    (f := Prod.fst) analyticAt_fst).mul
    ((analyticAt_fourierMonomial k _).comp (f := Prod.snd) analyticAt_snd)

theorem homologicalGenerator_periodic (p q : ComplexSpace n) (m : FourierIndex n) :
    homologicalGenerator f ω N (p, q + angleShift m) = homologicalGenerator f ω N (p, q) := by
  simp only [homologicalGenerator, fourierMonomial_periodic]

theorem homologicalCoeff_conj {p : ComplexSpace n} (hp : p ∈ G)
    (hω : ω (conjVec p) = conjVec (ω p)) (k : FourierIndex n) :
    homologicalCoeff f ω (conjVec p) (-k) = star (homologicalCoeff f ω p k) := by
  unfold homologicalCoeff
  rw [f.fourierCoeff_conj hp k, hω, indexPairing_neg, indexPairing_conj]
  simp [div_neg, neg_div]

theorem homologicalGenerator_conj {z : ComplexPhaseSpace n} (hz : z.1 ∈ G)
    (hω : ω (conjVec z.1) = conjVec (ω z.1)) :
    homologicalGenerator f ω N (conjPhase z) = star (homologicalGenerator f ω N z) := by
  change (∑ k ∈ lowModes n N, homologicalCoeff f ω (conjVec z.1) k *
    fourierMonomial k (conjVec z.2)) = _
  rw [← sum_lowModes_neg N (fun k => homologicalCoeff f ω (conjVec z.1) k *
    fourierMonomial k (conjVec z.2))]
  simp only [homologicalCoeff_conj f hz hω, fourierMonomial_conj_neg]
  simp [homologicalGenerator, star_mul, mul_comm]

theorem angle_fderiv_homologicalGenerator (p q v : ComplexSpace n) :
    fderiv ℂ (fun t => homologicalGenerator f ω N (p, t)) q v =
      ∑ k ∈ lowModes n N, homologicalCoeff f ω p k *
        ((I * indexPairing k v) * fourierMonomial k q) := by
  have hd : HasFDerivAt (fun t => homologicalGenerator f ω N (p, t))
      (∑ k ∈ lowModes n N, homologicalCoeff f ω p k • fderiv ℂ (fourierMonomial k) q) q := by
    apply HasFDerivAt.fun_sum
    intro k _
    exact (analyticAt_fourierMonomial k q).differentiableAt.hasFDerivAt.const_mul
      (homologicalCoeff f ω p k)
  rw [hd.fderiv]
  simp only [sum_apply, smul_apply,
    smul_eq_mul, fderiv_fourierMonomial]

theorem homological_equation {z : ComplexPhaseSpace n} (hz : z.1 ∈ G)
    (hω : AnalyticAt ℂ ω z.1) (hK : 0 < K) (hnr : FiniteNonresonant (ω z.1) K N)
    (hN : 0 < N) (hmean : f.angleAverage z.1 = 0) :
    (∑ j, ω z.1 j * qGradient (homologicalGenerator f ω N) z j) +
      fourierTruncation (f.fourierCoeff z.1) N z.2 = 0 := by
  have ha := analyticAt_homologicalGenerator f hz hω hK hnr
  rw [← angle_fderiv_eq_sum_qGradient ha, angle_fderiv_homologicalGenerator,
    fourierTruncation_eq_zero_add _ hN]
  change _ + (f.angleAverage z.1 + _) = 0
  rw [hmean, zero_add, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  have hd := hnr.ne_zero hK hk
  dsimp [homologicalCoeff]
  field_simp [hd]
  linear_combination (f.fourierCoeff z.1 k * fourierMonomial k z.2) * Complex.I_sq

end KamProject.Arnold1963
