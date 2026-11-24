/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SemiconcaveMollifierFamily

/-!
# Degeneracy of the limiting complex Hessian at a point of maximality

At a point `z₀` where a maximal plurisubharmonic function `u` has a second-order Peano
expansion with quadratic part `A`, the complex Hessians of any smooth plurisubharmonic
approximations whose real Hessians at `z₀` converge to `A` have determinants tending to zero:
the limiting matrix is positive semidefinite, and by the obstacle construction its Levi form
is not positive definite, so it is singular.

Source: Błocki, *The complex Monge–Ampère operator in pluripotential theory*, lecture notes,
proof of Theorem 2.3.1.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace Matrix
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- The complex Hessian matrix attached to a real bilinear form, with the same normalization
as `complexHessian`. -/
def complexHessianOfBilin (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun j k =>
  ((A (coordinateVector j) (coordinateVector k) +
      A (Complex.I • coordinateVector j) (Complex.I • coordinateVector k) : ℝ) : ℂ) / 4 +
    Complex.I * ((A (coordinateVector j) (Complex.I • coordinateVector k) -
      A (Complex.I • coordinateVector j) (coordinateVector k) : ℝ) : ℂ) / 4

/-- The Levi quadratic form attached to a real bilinear form. -/
def leviFormOfBilin (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ)
    (v : ComplexModel n) : ℝ := (A v v + A (Complex.I • v) (Complex.I • v)) / 4

theorem continuous_leviFormOfBilin (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    Continuous (leviFormOfBilin A) := by
  have h1 : Continuous fun v : ComplexModel n ↦ A v v :=
    A.continuous₂.comp₂ continuous_id continuous_id
  have h2 : Continuous fun v : ComplexModel n ↦ A (Complex.I • v) (Complex.I • v) :=
    A.continuous₂.comp₂ (continuous_const_smul _) (continuous_const_smul _)
  exact (h1.add h2).div_const 4

theorem leviFormOfBilin_smul (A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (t : ℝ)
    (v : ComplexModel n) : leviFormOfBilin A (t • v) = t ^ 2 * leviFormOfBilin A v := by
  have hIt : Complex.I • (t • v) = t • (Complex.I • v) := smul_comm _ _ _
  simp only [leviFormOfBilin, hIt, map_smul, _root_.smul_apply, smul_eq_mul]
  ring

theorem tendsto_ofReal {f : ℕ → ℝ} {a : ℝ} (h : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun k ↦ ((f k : ℝ) : ℂ)) atTop (𝓝 ((a : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.tendsto a).comp h

theorem tendsto_complexHessian_of_tendsto_realHessian {F : ℕ → ComplexModel n → ℝ}
    {z₀ : ComplexModel n} {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hconv : ∀ v w, Tendsto (fun k ↦ realHessian (F k) z₀ v w) atTop (𝓝 (A v w))) :
    Tendsto (fun k ↦ complexHessian (F k) z₀) atTop (𝓝 (complexHessianOfBilin A)) := by
  refine tendsto_pi_nhds.2 fun j ↦ tendsto_pi_nhds.2 fun k ↦ ?_
  simp only [complexHessian, complexHessianOfBilin]
  exact ((tendsto_ofReal ((hconv _ _).add (hconv _ _))).div_const 4).add
    ((tendsto_const_nhds.mul (tendsto_ofReal ((hconv _ _).sub (hconv _ _)))).div_const 4)

theorem tendsto_dotProduct_mulVec {M : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {H : Matrix (Fin n) (Fin n) ℂ} (h : Tendsto M atTop (𝓝 H)) (y : Fin n → ℂ) :
    Tendsto (fun k ↦ star y ⬝ᵥ ((M k).mulVec y)) atTop (𝓝 (star y ⬝ᵥ (H.mulVec y))) := by
  have hentry : ∀ i j, Tendsto (fun k ↦ M k i j) atTop (𝓝 (H i j)) := fun i j ↦
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j
  simp only [dotProduct, Matrix.mulVec, dotProduct, Pi.star_apply]
  refine tendsto_finsetSum _ fun i _ ↦ tendsto_const_nhds.mul ?_
  exact tendsto_finsetSum _ fun j _ ↦ (hentry i j).mul tendsto_const_nhds

/-- **The limiting complex Hessian at a point of maximality is singular.** -/
theorem tendsto_det_complexHessian_zero {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hmax : BedfordTaylor.IsMaximalPshOn Ω u) {F : ℕ → ComplexModel n → ℝ}
    (hF : ∀ k, ContDiff ℝ 2 (F k)) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω)
    (hlevi : ∀ k v, 0 ≤ leviForm (F k) z₀ v)
    {L : ComplexModel n →L[ℝ] ℝ} {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, A v w = A w v) (hpeano : HasPeanoExpansionAt u z₀ L A)
    (hconv : ∀ v w, Tendsto (fun k ↦ realHessian (F k) z₀ v w) atTop (𝓝 (A v w))) :
    Tendsto (fun k ↦ ((complexHessian (F k) z₀).det).re) atTop (𝓝 0) := by
  classical
  set H := complexHessianOfBilin A with hHdef
  have hmat := tendsto_complexHessian_of_tendsto_realHessian hconv
  -- Levi forms converge
  have hℓ : ∀ v, Tendsto (fun k ↦ leviForm (F k) z₀ v) atTop (𝓝 (leviFormOfBilin A v)) := by
    intro v
    simp only [leviForm, leviFormOfBilin]
    exact ((hconv v v).add (hconv _ _)).div_const 4
  have hℓnonneg : ∀ v, 0 ≤ leviFormOfBilin A v := fun v ↦
    ge_of_tendsto (hℓ v) (Eventually.of_forall fun k ↦ hlevi k v)
  -- the limit matrix is positive semidefinite
  have hquad : ∀ y : Fin n → ℂ,
      star y ⬝ᵥ (H.mulVec y) =
        ((leviFormOfBilin A (conjugateCoordinateCombination y) : ℝ) : ℂ) := by
    intro y
    have h1 := tendsto_dotProduct_mulVec hmat y
    have h2 : ∀ k, star y ⬝ᵥ ((complexHessian (F k) z₀).mulVec y)
        = ((leviForm (F k) z₀ (conjugateCoordinateCombination y) : ℝ) : ℂ) := fun k ↦
      complexHessian_dotProduct_mulVec_eq_leviForm ((hF k).contDiffAt) y
    have h3 : Tendsto (fun k ↦ star y ⬝ᵥ ((complexHessian (F k) z₀).mulVec y)) atTop
        (𝓝 ((leviFormOfBilin A (conjugateCoordinateCombination y) : ℝ) : ℂ)) := by
      simp only [h2]
      exact tendsto_ofReal (hℓ (conjugateCoordinateCombination y))
    exact tendsto_nhds_unique h1 h3
  have hherm : H.IsHermitian := by
    have hk : ∀ k, (complexHessian (F k) z₀).IsHermitian := fun k ↦
      complexHessian_isHermitian ((hF k).contDiffAt)
    have hconj : Tendsto (fun k ↦ (complexHessian (F k) z₀)ᴴ) atTop (𝓝 Hᴴ) := by
      refine tendsto_pi_nhds.2 fun j ↦ tendsto_pi_nhds.2 fun l ↦ ?_
      simp only [conjTranspose_apply]
      exact ((continuous_star (R := ℂ)).tendsto (H l j)).comp
        (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hmat l) j)
    have hself : Tendsto (fun k ↦ (complexHessian (F k) z₀)ᴴ) atTop (𝓝 H) := by
      have hfun : (fun k ↦ (complexHessian (F k) z₀)ᴴ) = fun k ↦ complexHessian (F k) z₀ :=
        funext fun k ↦ hk k
      rw [hfun]
      exact hmat
    exact tendsto_nhds_unique hconj hself
  have hPSD : H.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun y ↦ ?_
    rw [hquad y]
    exact Complex.zero_le_real.mpr (hℓnonneg _)
  -- maximality forbids a positive definite Levi form
  have hnotPD : ¬ ∃ c : ℝ, 0 < c ∧ ∀ v : ComplexModel n, c * ‖v‖ ^ 2 ≤ leviFormOfBilin A v := by
    rintro ⟨c, hc, hcle⟩
    exact false_of_isMaximalPshOn_of_hasPeanoExpansion hmax hz₀ hsymm hpeano hc hcle
  -- hence a unit vector on which the Levi form vanishes
  obtain ⟨v₀, hv₀norm, hv₀⟩ : ∃ v₀ : ComplexModel n, ‖v₀‖ = 1 ∧ leviFormOfBilin A v₀ = 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      refine hnotPD ⟨1, one_pos, fun v ↦ ?_⟩
      have hv : v = 0 := by
        subst hn
        ext i
        exact absurd i.2 (by simp)
      rw [hv]
      simpa using hℓnonneg 0
    · have hne : (sphere (0 : ComplexModel n) 1).Nonempty := by
        refine ⟨coordinateVector ⟨0, hn⟩, ?_⟩
        simp [mem_sphere_iff_norm, coordinateVector, PiLp.norm_single]
      have hcomp : IsCompact (sphere (0 : ComplexModel n) 1) := by
        have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
        exact isCompact_sphere 0 1
      obtain ⟨v₀, hv₀mem, hv₀min⟩ :=
        hcomp.exists_isMinOn hne (continuous_leviFormOfBilin A).continuousOn
      have hv₀norm : ‖v₀‖ = 1 := by simpa [mem_sphere_iff_norm] using hv₀mem
      refine ⟨v₀, hv₀norm, le_antisymm ?_ (hℓnonneg v₀)⟩
      by_contra hpos
      push Not at hpos
      refine hnotPD ⟨leviFormOfBilin A v₀, hpos, fun v ↦ ?_⟩
      rcases eq_or_ne v 0 with rfl | hv
      · simpa using hℓnonneg 0
      · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        have hw : ‖v‖⁻¹ • v ∈ sphere (0 : ComplexModel n) 1 := by
          simp [mem_sphere_iff_norm, norm_smul,
            inv_mul_cancel₀ hvn.ne']
        have hmin := hv₀min hw
        simp only [Set.mem_ofPred_eq] at hmin
        have hhom : leviFormOfBilin A (‖v‖⁻¹ • v) = (‖v‖⁻¹) ^ 2 * leviFormOfBilin A v :=
          leviFormOfBilin_smul A _ v
        rw [hhom] at hmin
        have hsq : (0:ℝ) < ‖v‖ ^ 2 := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hmin hsq.le
        have hcancel : ‖v‖ ^ 2 * ((‖v‖⁻¹) ^ 2 * leviFormOfBilin A v)
            = leviFormOfBilin A v := by
          field_simp
        rw [hcancel] at hscaled
        nlinarith [hscaled]
  -- the limit matrix is singular
  set x : Fin n → ℂ := fun i ↦ star (v₀ i) with hxdef
  have hxne : x ≠ 0 := by
    intro hx
    have hv : v₀ = 0 := by
      ext i
      have := congrFun hx i
      simpa [hxdef] using this
    rw [hv] at hv₀norm
    simp at hv₀norm
  have hxzero : star x ⬝ᵥ (H.mulVec x) = 0 := by
    rw [hquad x, hxdef, conjugateCoordinateCombination_star v₀, hv₀]
    simp
  have hdet0 : H.det = 0 := by
    by_contra hne
    have hpd : H.PosDef := by
      refine (Matrix.IsHermitian.posDef_iff_eigenvalues_pos hherm).mpr fun i ↦ ?_
      rcases (hPSD.eigenvalues_nonneg i).lt_or_eq with h | h
      · exact h
      · exfalso
        refine hne ?_
        rw [hherm.det_eq_prod_eigenvalues]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [← h]
        simp
    have hpos := hpd.re_dotProduct_pos hxne
    rw [hxzero] at hpos
    simp at hpos
  have hdet : Tendsto (fun k ↦ (complexHessian (F k) z₀).det) atTop (𝓝 H.det) :=
    (Continuous.matrix_det continuous_id).tendsto H |>.comp hmat
  rw [hdet0] at hdet
  have hre := (Complex.continuous_re.tendsto (0 : ℂ)).comp hdet
  simpa [Function.comp_def] using hre

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
