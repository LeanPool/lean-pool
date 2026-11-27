/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CoefficientWeakStarHomeomorphism
public import LeanPool.VacuumBellSeparation.Bell.CommutantVectorDomination
public import LeanPool.VacuumBellSeparation.Bell.SignedBellCorrelation
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Normal-state real expectations determine weak convergence of self-adjoint
operators in the original representation. Uniform operator bounds then
give the literal weak-star topology of the proved coefficient predual.
The proof normalizes each original vector and uses complex polarization;
it does not assume a representation theorem for arbitrary normal states.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open HC00 Filter
open scoped Topology ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {l : Filter ι}

theorem normalState_complex_limit_of_real_limit
    (M : VonNeumannAlgebra H) (T : ι → M.toStarSubalgebra) (L : M.toStarSubalgebra)
    (hT : ∀ i, IsSelfAdjoint (T i)) (hL : IsSelfAdjoint L)
    (φ : NormalStateSpace M)
    (h : Tendsto (fun i => (φ.1 (T i)).re) l (𝓝 (φ.1 L).re)) :
    Tendsto (fun i => φ.1 (T i)) l (𝓝 (φ.1 L)) := by
  have he (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      ((φ.1 a).re : ℂ) = φ.1 a :=
    Complex.conj_eq_iff_re.mp (stateFunctional_isSelfAdjoint M ⟨φ.1, φ.2.1⟩ ha).star_eq
  simpa only [Function.comp_def, he _ (hT _), he L hL] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp h

theorem selfAdjoint_wot_limit_of_normalState_real_limits
    (M : VonNeumannAlgebra H) (T : ι → M.toStarSubalgebra) (L : M.toStarSubalgebra)
    (hT : ∀ i, IsSelfAdjoint (T i)) (hL : IsSelfAdjoint L)
    (h : ∀ φ : NormalStateSpace M,
      Tendsto (fun i => (φ.1 (T i)).re) l (𝓝 (φ.1 L).re)) :
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i : H →L[ℂ] H)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM (L : H →L[ℂ] H))) := by
  have hunit (x : H) (hx : ‖x‖ = 1) :
      Tendsto (fun i => ⟪x, (T i : H →L[ℂ] H) x⟫_ℂ) l
        (𝓝 ⟪x, (L : H →L[ℂ] H) x⟫_ℂ) :=
    normalState_complex_limit_of_real_limit M T L hT hL
      (SW88.vectorNormalState M x hx) (h _)
  have hdiag (x : H) :
      Tendsto (fun i => ⟪x, (T i : H →L[ℂ] H) x⟫_ℂ) l
        (𝓝 ⟪x, (L : H →L[ℂ] H) x⟫_ℂ) := by
    by_cases hx : x = 0
    · simp only [hx, inner_zero_left]
      exact tendsto_const_nhds
    · let u := reehSchliederUnitVector x
      have he (a : M.toStarSubalgebra) :
          ⟪x, (a : H →L[ℂ] H) x⟫_ℂ =
            (‖x‖ : ℂ) ^ 2 * ⟪u, (a : H →L[ℂ] H) u⟫_ℂ := by
        calc
          _ = ⟪(‖x‖ : ℂ) • u, (a : H →L[ℂ] H) ((‖x‖ : ℂ) • u)⟫_ℂ := by
            rw [norm_smul_reehSchliederUnitVector hx]
          _ = _ := by
            rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
            ring
      simpa only [he] using
        (hunit u (reehSchliederUnitVector_norm hx)).const_mul ((‖x‖ : ℂ) ^ 2)
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
  intro y x
  change Tendsto (fun i => ⟪x, (T i : H →L[ℂ] H) y⟫_ℂ) l
    (𝓝 ⟪x, (L : H →L[ℂ] H) y⟫_ℂ)
  have hpol (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) :
      ⟪x, (a : H →L[ℂ] H) y⟫_ℂ =
        (⟪x + y, (a : H →L[ℂ] H) (x + y)⟫_ℂ -
          ⟪x - y, (a : H →L[ℂ] H) (x - y)⟫_ℂ -
          Complex.I * ⟪x + Complex.I • y, (a : H →L[ℂ] H) (x + Complex.I • y)⟫_ℂ +
          Complex.I * ⟪x - Complex.I • y, (a : H →L[ℂ] H) (x - Complex.I • y)⟫_ℂ) / 4 := by
    have hs : IsSelfAdjoint (a : H →L[ℂ] H) :=
      congrArg (fun b : M.toStarSubalgebra => (b : H →L[ℂ] H)) ha.star_eq
    have hp := inner_map_polarization' (a : H →L[ℂ] H).toLinearMap x y
    change ⟪(a : H →L[ℂ] H) x, y⟫_ℂ =
      (⟪(a : H →L[ℂ] H) (x + y), x + y⟫_ℂ -
        ⟪(a : H →L[ℂ] H) (x - y), x - y⟫_ℂ -
        Complex.I * ⟪(a : H →L[ℂ] H) (x + Complex.I • y), x + Complex.I • y⟫_ℂ +
        Complex.I * ⟪(a : H →L[ℂ] H) (x - Complex.I • y), x - Complex.I • y⟫_ℂ) / 4 at hp
    have hsxy (u v : H) :
        ⟪(a : H →L[ℂ] H) u, v⟫_ℂ = ⟪u, (a : H →L[ℂ] H) v⟫_ℂ :=
      hs.isSymmetric u v
    simpa only [hsxy] using hp
  simpa only [hpol _ (hT _), hpol L hL] using
    ((((hdiag (x + y)).sub (hdiag (x - y))).sub
      ((hdiag (x + Complex.I • y)).const_mul Complex.I)).add
        ((hdiag (x - Complex.I • y)).const_mul Complex.I)).div_const 4

theorem selfAdjoint_coefficientWeak_limit_of_normalState_real_limits
    (M : VonNeumannAlgebra H) (T : ι → M.toStarSubalgebra) (L : M.toStarSubalgebra)
    (hT : ∀ i, IsSelfAdjoint (T i)) (hL : IsSelfAdjoint L)
    (R : ℝ) (hb : ∀ i, ‖T i‖ ≤ R) (hbL : ‖L‖ ≤ R)
    (h : ∀ φ : NormalStateSpace M,
      Tendsto (fun i => (φ.1 (T i)).re) l (𝓝 (φ.1 L).re)) :
    Tendsto (β := CoefficientWeakAlgebra M) (fun i => T i) l
      (nhds (X := CoefficientWeakAlgebra M) L) := by
  let F : ι → vnaWOTBall M R := fun i =>
    ⟨ContinuousLinearMapWOT.ofCLM (T i : H →L[ℂ] H), (T i).2, hb i⟩
  let G : vnaWOTBall M R :=
    ⟨ContinuousLinearMapWOT.ofCLM (L : H →L[ℂ] H), L.2, hbL⟩
  have hw : Tendsto F l (𝓝 G) := tendsto_subtype_rng.mpr
    (selfAdjoint_wot_limit_of_normalState_real_limits M T L hT hL h)
  exact (continuous_boundedWOT_to_coefficientWeak M R).continuousAt.tendsto.comp hw

end VacuumBellSeparation.Bipartite
