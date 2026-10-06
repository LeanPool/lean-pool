/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingFourierDamped
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalBounds

/-!
# Classical spatial derivatives of high-order inverse Fourier fields

The extra Bessel weight places every finite coordinate word within the
quadratic-growth inverse Fourier field theorem. Differentiation then
appends the corresponding coordinate symbol.
-/

public section

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real


noncomputable section

namespace ESS

open CKN CKN.Foundation.Parabolic

/-- The ordered coordinate multiplier is continuous in frequency. -/
theorem lps_fourierWordSymbol_continuous
    (α : List (Fin 3)) :
    Continuous (lps_fourierWordSymbol α) := by
  induction α with
  | nil =>
      change Continuous (fun _ : L2Vec3 => (1 : ℂ))
      exact continuous_const
  | cons j α ih =>
      have hj := CKN.Leray.regR12CoordSymbol_continuous j
      change Continuous (fun ξ : L2Vec3 =>
        CKN.Leray.regR12CoordSymbol j ξ * lps_fourierWordSymbol α ξ)
      exact hj.mul ih

/-- The damped ordered multiplier is continuous in frequency. -/
theorem lps_dampedFourierWordSymbol_continuous
    (n : ℕ) (α : List (Fin 3)) :
    Continuous (lps_dampedFourierWordSymbol n α) := by
  have hb : Continuous (fun ξ : L2Vec3 =>
      (((1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_norm.pow 2)).rpow_const
        fun ξ => Or.inl
          (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne')
  exact (lps_fourierWordSymbol_continuous α).mul hb

/-- A high-order inverse Fourier field has the next classical spatial
partial, represented by the appended coordinate word
(`prop:lps-smoothing`). -/
theorem lps_dampedSpaceTimeField_spatialPartial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length + 1 ≤ 2 * (n + 1))
    (c : E →L[ℝ] ℝ)
    (G : ℝ → Lp E 2 (volume : Measure L2Vec3))
    (z : ParabolicPoint) :
    DifferentiableAt ℝ
      (fun x : Vec3 => CKN.Leray.regR12SpaceTimeField c
        (lps_dampedFourierWordSymbol n α) G (x, z.2)) z.1 ∧
    ∀ j : Fin 3,
      spatialPartial
        (CKN.Leray.regR12SpaceTimeField c
          (lps_dampedFourierWordSymbol n α) G) j z =
      CKN.Leray.regR12SpaceTimeField c
        (lps_dampedFourierWordSymbol n (α ++ [j])) G z := by
  have hα₀ : α.length ≤ 2 * (n + 1) := by omega
  have hC : 0 ≤ (2 * π) ^ α.length := by positivity
  have h := CKN.Leray.regR12SpaceTimeField_spatialPartial c
    (lps_dampedFourierWordSymbol n α)
    (lps_dampedFourierWordSymbol_continuous n α).aestronglyMeasurable
    ((2 * π) ^ α.length) hC
    (lps_dampedFourierWordSymbol_norm_le n α hα₀)
    G (lps_dampedFourierWordSymbol_first_moment_le n α hα) z
  refine ⟨h.1, fun j => ?_⟩
  rw [h.2 j]
  congr 1
  funext ξ
  unfold lps_dampedFourierWordSymbol
  rw [lps_fourierWordSymbol_append]
  ring

/-- Every ordered classical spatial derivative of the base inverse
Fourier field is represented by its damped coordinate multiplier,
through the chosen Bessel order (`prop:lps-smoothing`). -/
theorem lps_dampedSpaceTimeField_wordDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1))
    (c : E →L[ℝ] ℝ)
    (G : ℝ → Lp E 2 (volume : Measure L2Vec3))
    (t : ℝ) :
    wordDeriv α (fun x : Vec3 =>
      CKN.Leray.regR12SpaceTimeField c
        (lps_dampedFourierWordSymbol n []) G (x, t)) =
    fun x : Vec3 => CKN.Leray.regR12SpaceTimeField c
      (lps_dampedFourierWordSymbol n α) G (x, t) := by
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α j ih =>
      have hα₀ : α.length ≤ 2 * (n + 1) := by
        simp only [List.length_append, List.length_singleton] at hα
        omega
      have hα₁ : α.length + 1 ≤ 2 * (n + 1) := by
        simpa only [List.length_append, List.length_singleton] using hα
      rw [wordDeriv_append, ih hα₀]
      funext x
      exact (lps_dampedSpaceTimeField_spatialPartial
        n α hα₁ c G (x, t)).2 j

/-- Continuous higher Bessel frequency curves give jointly continuous
ordered spatial derivative fields on the product space
(`prop:lps-smoothing`). -/
theorem lps_dampedSpaceTimeField_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1))
    (c : E →L[ℝ] ℝ)
    (G : ℝ → Lp E 2 (volume : Measure L2Vec3))
    (hG : Continuous G) :
    Continuous (fun z : Vec3 × ℝ =>
      CKN.Leray.regR12SpaceTimeField c
        (lps_dampedFourierWordSymbol n α) G (z.1, z.2)) := by
  exact CKN.Leray.regR12SpaceTimeField_continuous c
    (lps_dampedFourierWordSymbol n α)
    (lps_dampedFourierWordSymbol_continuous n α).aestronglyMeasurable
    ((2 * π) ^ α.length) (by positivity)
    (lps_dampedFourierWordSymbol_norm_le n α hα) G hG

/-- The weighted frequency representative of each ordered spatial
word remains in `L²` (`prop:lps-smoothing`). -/
theorem lps_dampedSpaceTimeField_frequency_memLp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1))
    (G : Lp E 2 (volume : Measure L2Vec3)) :
    MemLp (fun ξ : L2Vec3 =>
      lps_dampedFourierWordSymbol n α ξ •
        (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
          (G : L2Vec3 → E) ξ) 2 volume := by
  let C : ℝ := (2 * π) ^ α.length
  have hG : MemLp (fun ξ : L2Vec3 => C * ‖(G : L2Vec3 → E) ξ‖)
      2 volume := (Lp.memLp G).norm.const_mul C
  have hmeas : AEStronglyMeasurable
      (fun ξ : L2Vec3 =>
        lps_dampedFourierWordSymbol n α ξ •
          (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
            (G : L2Vec3 → E) ξ) volume :=
    (lps_dampedFourierWordSymbol_continuous n α).aestronglyMeasurable.smul
      (CKN.Leray.regR12Weight_continuous.aestronglyMeasurable.smul
        (Lp.aestronglyMeasurable G))
  refine hG.mono' hmeas (Filter.Eventually.of_forall fun ξ => ?_)
  rw [smul_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right
    (lps_dampedFourierWordSymbol_weighted_norm_le n α hα ξ)
    (norm_nonneg _)

/-- Every spatial slice of a damped high-order inverse Fourier field
is square-integrable (`prop:lps-smoothing`). -/
theorem lps_dampedSpaceTimeField_slice_memLp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (n : ℕ) (α : List (Fin 3))
    (hα : α.length ≤ 2 * (n + 1))
    (c : E →L[ℝ] ℝ)
    (G : Lp E 2 (volume : Measure L2Vec3)) :
    MemLp (fun x : Vec3 => c (CKN.Leray.regR12WeightedField
      (lps_dampedFourierWordSymbol n α) G (WithLp.toLp 2 x)))
      2 volume := by
  let M : L2Vec3 → ℂ := lps_dampedFourierWordSymbol n α
  let h : L2Vec3 → E := fun ξ => M ξ •
    (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ) •
      (G : L2Vec3 → E) ξ
  have hmem : MemLp h 2 volume :=
    lps_dampedSpaceTimeField_frequency_memLp n α hα G
  let H : Lp E 2 (volume : Measure L2Vec3) :=
    (Lp.fourierTransformₗᵢ L2Vec3 E).symm (hmem.toLp h)
  have hGH :
      ((Lp.fourierTransformₗᵢ L2Vec3 E H :
        Lp E 2 (volume : Measure L2Vec3)) : L2Vec3 → E) =ᵐ[volume] h := by
    simp only [H, LinearIsometryEquiv.apply_symm_apply]
    exact hmem.coeFn_toLp
  have hrep := CKN.Leray.regR12WeightedField_ae_eq M
    (lps_dampedFourierWordSymbol_continuous n α).aestronglyMeasurable
    ((2 * π) ^ α.length) (by positivity)
    (lps_dampedFourierWordSymbol_norm_le n α hα) G H hGH
  have hrepVec :=
    CKN.Leray.vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae_eq_comp hrep
  have hHmem : MemLp
      (fun x : Vec3 => (H : L2Vec3 → E) (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp H).comp_measurePreserving
      CKN.Leray.vec3ToL2Vec3_measurePreserving
  have hfield : MemLp
      (fun x : Vec3 => CKN.Leray.regR12WeightedField M G (WithLp.toLp 2 x))
      2 volume := (memLp_congr_ae hrepVec).2 hHmem
  exact c.comp_memLp' hfield

end ESS
