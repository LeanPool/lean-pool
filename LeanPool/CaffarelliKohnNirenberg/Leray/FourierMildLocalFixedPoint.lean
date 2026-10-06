/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The contraction on the local mild trajectory ball

The fixed-interval mild map is a self-map and a strict contraction on the
closed divergence-free ball in `lem:reg-local-mild`.
-/

public section

open MeasureTheory
open Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The local mild radius parameter `M` from `eq:reg-lifespan`. -/
@[expose]
def regularizedMildLocalM (b : RealVectorL2) : ℝ := 1 + ‖b‖

private theorem regularizedMildAeps_eq_operatorConstant (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) :
    regularizedMildAeps ρ ε =
      regularizedMildMollifierConstant ρ ε / Real.sqrt (2 * Real.exp 1) := by
  rw [regularizedMildAeps, regularizedMildMollifierConstant_eq_profile ρ ε hε]

private theorem regularizedMildLocalLifespan_sqrt
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) :
    Real.sqrt (regularizedMildLocalLifespan ρ ε b) =
      (16 * regularizedMildAeps ρ ε * regularizedMildLocalM  b)⁻¹ := by
  have hbase : 0 < 16 * regularizedMildAeps ρ ε * regularizedMildLocalM b := by
    dsimp [regularizedMildLocalM]
    positivity [regularizedMildAeps_pos ρ ε hε]
  have hbase' : 0 < 16 * regularizedMildAeps ρ ε * (1 + ‖b‖) := by
    simpa [regularizedMildLocalM] using hbase
  rw [regularizedMildLocalLifespan, regularizedMildLocalM,
    Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hbase')]

/-- The Abel estimate at the lifespan in `eq:reg-lifespan` maps a radius
`2M` tensor bound to an integral bound of `M/2`. -/
theorem regularizedMildBallAbelBalance
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) :
    2 * ((regularizedMildMollifierConstant ρ ε *
        (2 * regularizedMildLocalM b) ^ 2) / Real.sqrt (2 * Real.exp 1)) *
      Real.sqrt (regularizedMildLocalLifespan ρ ε b) =
        regularizedMildLocalM b / 2 := by
  let A := regularizedMildAeps ρ ε
  let M := regularizedMildLocalM b
  have hA : A = regularizedMildMollifierConstant ρ ε /
      Real.sqrt (2 * Real.exp 1) := by
    exact regularizedMildAeps_eq_operatorConstant ρ ε hε
  have hApos : 0 < A := by
    exact regularizedMildAeps_pos ρ ε hε
  have hMpos : 0 < M := by
    dsimp [M, regularizedMildLocalM]
    positivity
  have hroot : Real.sqrt (regularizedMildLocalLifespan ρ ε b) =
      (16 * A * M)⁻¹ := by
    simpa [A, M] using regularizedMildLocalLifespan_sqrt ρ ε hε b
  calc
    2 * ((regularizedMildMollifierConstant ρ ε * (2 * M) ^ 2) /
        Real.sqrt (2 * Real.exp 1)) *
      Real.sqrt (regularizedMildLocalLifespan ρ ε b) =
        2 * (regularizedMildMollifierConstant ρ ε /
          Real.sqrt (2 * Real.exp 1)) * (2 * M) ^ 2 *
            Real.sqrt (regularizedMildLocalLifespan ρ ε b) := by ring
    _ = 2 * A * (2 * M) ^ 2 * (16 * A * M)⁻¹ := by rw [← hA, hroot]
    _ = M / 2 := by
      field_simp [ne_of_gt hApos, ne_of_gt hMpos]
      ring

private theorem regularizedMildContractionAbelBalance
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (D : ℝ) :
    2 * ((regularizedMildMollifierConstant ρ ε *
        (4 * regularizedMildLocalM b) * D) / Real.sqrt (2 * Real.exp 1)) *
      Real.sqrt (regularizedMildLocalLifespan ρ ε b) = D / 2 := by
  let A := regularizedMildAeps ρ ε
  let M := regularizedMildLocalM b
  have hA : A = regularizedMildMollifierConstant ρ ε /
      Real.sqrt (2 * Real.exp 1) :=
    regularizedMildAeps_eq_operatorConstant ρ ε hε
  have hApos : 0 < A := regularizedMildAeps_pos ρ ε hε
  have hMpos : 0 < M := by
    dsimp [M, regularizedMildLocalM]
    positivity
  have hroot : Real.sqrt (regularizedMildLocalLifespan ρ ε b) =
      (16 * A * M)⁻¹ := by
    simpa [A, M] using regularizedMildLocalLifespan_sqrt ρ ε hε b
  calc
    2 * ((regularizedMildMollifierConstant ρ ε * (4 * M) * D) /
        Real.sqrt (2 * Real.exp 1)) *
      Real.sqrt (regularizedMildLocalLifespan ρ ε b) =
        2 * (regularizedMildMollifierConstant ρ ε /
          Real.sqrt (2 * Real.exp 1)) * (4 * M) * D *
            Real.sqrt (regularizedMildLocalLifespan ρ ε b) := by ring
    _ = 2 * A * (4 * M) * D * (16 * A * M)⁻¹ := by rw [← hA, hroot]
    _ = D / 2 := by
      field_simp [ne_of_gt hApos, ne_of_gt hMpos]
      ring

/-- The local mild map has contraction factor one half on the closed ball of
radius `2(1+‖b‖)`. -/
theorem regularizedMildLocalMap_sub_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    (u v : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
      RealVectorL2))
    (hu : ∀ t, ‖u t‖ ≤ 2 * regularizedMildLocalM b)
    (hv : ∀ t, ‖v t‖ ≤ 2 * regularizedMildLocalM b) :
    ‖regularizedMildLocalMap ρ ε hε b (regularizedMildLocalLifespan ρ ε b)
        (regularizedMildLocalLifespan_pos ρ ε hε b).le u -
      regularizedMildLocalMap ρ ε hε b (regularizedMildLocalLifespan ρ ε b)
        (regularizedMildLocalLifespan_pos ρ ε hε b).le v‖ ≤
      (1 / 2 : ℝ) * ‖u - v‖ := by
  let T := regularizedMildLocalLifespan ρ ε b
  let hT : 0 ≤ T := (regularizedMildLocalLifespan_pos ρ ε hε b).le
  let F := regularizedMildClampedTensorTrajectory ρ ε hε T hT u
  let G := regularizedMildClampedTensorTrajectory ρ ε hε T hT v
  let M := regularizedMildLocalM b
  let C := regularizedMildMollifierConstant ρ ε * (2 * M) ^ 2
  let D := regularizedMildMollifierConstant ρ ε * (4 * M) * ‖u - v‖
  have hFcont : Continuous F :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT u
  have hGcont : Continuous G :=
    regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT v
  have hFC : ∀ s, ‖F s‖ ≤ C := by
    have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
    have hR : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMnonneg
    simpa [F, C, M] using
      regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT u
        (2 * M) hR (by simpa [M, regularizedMildLocalM] using hu)
  have hGC : ∀ s, ‖G s‖ ≤ C := by
    have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
    have hR : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMnonneg
    simpa [G, C, M] using
      regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT v
        (2 * M) hR (by simpa [M, regularizedMildLocalM] using hv)
  have hFGcont : Continuous (fun s => F s - G s) := hFcont.sub hGcont
  have hFGC : ∀ s, ‖F s - G s‖ ≤ D := by
    have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
    have hR : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMnonneg
    have hbound :=
      regularizedMildClampedTensorTrajectory_sub_norm_le ρ ε hε T hT u v
        (2 * M) hR (by simpa [M, regularizedMildLocalM] using hu)
        (by simpa [M, regularizedMildLocalM] using hv)
    intro s
    calc
      ‖F s - G s‖ ≤
          regularizedMildMollifierConstant ρ ε * (2 * (2 * M)) * ‖u - v‖ := by
        simpa [F, G] using hbound s
      _ = D := by dsimp [D]; ring
  have hK : 0 ≤ regularizedMildMollifierConstant ρ ε := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := mul_nonneg hK (sq_nonneg (2 * M))
  have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
  have h4M : 0 ≤ 4 * M := mul_nonneg (by norm_num) hMnonneg
  have hK4M : 0 ≤ regularizedMildMollifierConstant ρ ε * (4 * M) :=
    mul_nonneg hK h4M
  have hD : 0 ≤ D := mul_nonneg hK4M (norm_nonneg _)
  have hFint (t : ℝ) :
      IntervalIntegrable (fun τ => mildShiftedStokesIntegrand F t τ) volume 0 T :=
    mildShiftedStokesIntegrand_intervalIntegrable F hFcont C hFC hC T t hT
  have hGint (t : ℝ) :
      IntervalIntegrable (fun τ => mildShiftedStokesIntegrand G t τ) volume 0 T :=
    mildShiftedStokesIntegrand_intervalIntegrable G hGcont C hGC hC T t hT
  have hFGpoint (t τ : ℝ) :
      mildShiftedStokesIntegrand (fun s => F s - G s) t τ =
        mildShiftedStokesIntegrand F t τ - mildShiftedStokesIntegrand G t τ := by
    by_cases h : 0 < τ ∧ τ < t
    · simp only [mildShiftedStokesIntegrand, h]
      change realStokesOperator h.1 (F (t - τ) - G (t - τ)) =
        realStokesOperator h.1 (F (t - τ)) - realStokesOperator h.1 (G (t - τ))
      rw [show F (t - τ) - G (t - τ) =
        F (t - τ) + (-1 : ℝ) • G (t - τ) by
          simp only [sub_eq_add_neg, neg_one_smul],
        realStokesOperator_add h.1, realStokesOperator_smul h.1 (-1)]
      simp only [neg_one_smul, sub_eq_add_neg]
    · simp [mildShiftedStokesIntegrand, h]
  have hFGintegral (t : ℝ) :
      (∫ τ in (0 : ℝ)..T,
        mildShiftedStokesIntegrand (fun s => F s - G s) t τ) =
        (∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t τ) -
          ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand G t τ := by
    calc
      (∫ τ in (0 : ℝ)..T,
          mildShiftedStokesIntegrand (fun s => F s - G s) t τ) =
        ∫ τ in (0 : ℝ)..T,
          (mildShiftedStokesIntegrand F t τ -
            mildShiftedStokesIntegrand G t τ) := by
              congr 1
              funext τ
              exact hFGpoint t τ
      _ = _ := intervalIntegral.integral_sub (hFint t) (hGint t)
  have hpointwise : ∀ t : RegularizedMildTimeInterval T,
      ‖regularizedMildLocalMap ρ ε hε b T hT u t -
          regularizedMildLocalMap ρ ε hε b T hT v t‖ ≤ ‖u - v‖ / 2 := by
    intro t
    rw [regularizedMildLocalMap_eq_shifted, regularizedMildLocalMap_eq_shifted]
    have hcancel :
        (realHeatOperator t.1 t.2.1 b -
          ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ) -
        (realHeatOperator t.1 t.2.1 b -
          ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand G t.1 τ) =
          -((∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ) -
            ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand G t.1 τ) := by
      abel
    rw [hcancel, norm_neg, ← hFGintegral]
    exact (mildShiftedStokesIntegral_norm_le (fun s => F s - G s)
      D hFGC hD T t.1 hT).trans_eq
        (regularizedMildContractionAbelBalance ρ ε hε b ‖u - v‖)
  apply (regularizedMildTrajectory_norm_le_iff T
    (regularizedMildLocalMap ρ ε hε b T hT u -
      regularizedMildLocalMap ρ ε hε b T hT v)
    ((1 / 2 : ℝ) * ‖u - v‖) (by positivity)).2
  intro t
  have hpoint := hpointwise t
  simpa [D, M, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpoint

@[expose]
def regularizedMildLocalBall (T M : ℝ) :
    Set (C(RegularizedMildTimeInterval T, RealVectorL2)) :=
  {u | ∀ t, RegularizedMildJData (u t) ∧ ‖u t‖ ≤ 2 * M}

private theorem regularizedMildLocalBall_isClosed (T M : ℝ) :
    IsClosed (regularizedMildLocalBall T M) := by
  rw [show regularizedMildLocalBall T M =
      ⋂ t, {u : C(RegularizedMildTimeInterval T, RealVectorL2) |
        RegularizedMildJData (u t) ∧ ‖u t‖ ≤ 2 * M} by
    ext u
    simp [regularizedMildLocalBall]]
  refine isClosed_iInter fun t => ?_
  have heval : Continuous fun u : C(RegularizedMildTimeInterval T, RealVectorL2) => u t :=
    continuous_eval_const t
  exact (regularizedMildJData_isClosed.preimage heval).inter
    (isClosed_Iic.preimage (continuous_norm.comp heval))

private theorem regularizedMildJData_zero :
    RegularizedMildJData (0 : RealVectorL2) := by
  have hcomp : MemLp
      (fun x : Vec3 => (0 : RealVectorL2) (WithLp.toLp 2 x)) 2 volume :=
    (Lp.memLp (0 : RealVectorL2)).comp_measurePreserving
      vec3ToL2Vec3_measurePreserving
  change CKN.IsInJ (realVectorL2Representative (0 : RealVectorL2))
  apply CKN.weakDivFreeL2_isInJ
  refine ⟨?_, ?_⟩
  · change MemLp
      (fun x : Vec3 =>
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))
          ((0 : RealVectorL2) (WithLp.toLp 2 x))) 2 volume
    exact hcomp.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  · intro ψ
    have hz : realVectorL2Representative (0 : RealVectorL2) =ᵐ[volume]
        fun _ : Vec3 => 0 := by
      filter_upwards [] with x
      simp [realVectorL2Representative]
    have hintegrand :
        (fun x : Vec3 => ∑ i : Fin 3,
          realVectorL2Representative (0 : RealVectorL2) x i * ψ.partialDeriv i x) =ᵐ[volume]
        fun _ => 0 := by
      filter_upwards [hz] with x hx
      simp [hx]
    rw [integral_congr_ae hintegrand]
    simp

/-- A fixed point of the local mild map gives the local solution and remains
in the closed divergence-free ball. -/
theorem regularizedMildLocalFixedPoint
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (b : RealVectorL2)
    (hb : RegularizedMildJData b) :
    ∃ u : C(RegularizedMildTimeInterval (regularizedMildLocalLifespan ρ ε b),
        RealVectorL2),
      IsRegularizedMildTrajectory ρ ε hε b
        (regularizedMildLocalLifespan ρ ε b) u ∧
      (∀ t, RegularizedMildJData (u t) ∧
        ‖u t‖ ≤ 2 * regularizedMildLocalM b) := by
  let T := regularizedMildLocalLifespan ρ ε b
  let hT : 0 ≤ T := (regularizedMildLocalLifespan_pos ρ ε hε b).le
  let M := regularizedMildLocalM b
  let S := regularizedMildLocalBall T M
  let f : C(RegularizedMildTimeInterval T, RealVectorL2) →
      C(RegularizedMildTimeInterval T, RealVectorL2) :=
    regularizedMildLocalMap ρ ε hε b T hT
  have hmap : MapsTo f S S := by
    intro u hu t
    rcases hu t with ⟨_huJ, huNorm⟩
    constructor
    · exact regularizedMildLocalMap_isInJ ρ ε hε b hb T hT
        (regularizedMildLocalLifespan_pos ρ ε hε b) u t
    · let F := regularizedMildClampedTensorTrajectory ρ ε hε T hT u
      let C := regularizedMildMollifierConstant ρ ε * (2 * M) ^ 2
      have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
      have hR : 0 ≤ 2 * M := mul_nonneg (by norm_num) hMnonneg
      have hFcont : Continuous F :=
        regularizedMildClampedTensorTrajectory_continuous ρ ε hε T hT u
      have hFC : ∀ s, ‖F s‖ ≤ C := by
        simpa [F, C] using
          regularizedMildClampedTensorTrajectory_norm_le ρ ε hε T hT u
            (2 * M) hR (by simpa [M, regularizedMildLocalM] using fun q => (hu q).2)
      have hK : 0 ≤ regularizedMildMollifierConstant ρ ε := ENNReal.toReal_nonneg
      have hC : 0 ≤ C := mul_nonneg hK (sq_nonneg (2 * M))
      have hI := mildShiftedStokesIntegral_norm_le F C hFC hC T t.1 hT
      have hheat := realHeatOperator_norm_le t.1 t.2.1 b
      have hAbel := regularizedMildBallAbelBalance ρ ε hε b
      have hnorm : ‖f u t‖ ≤ ‖b‖ + M / 2 := by
        rw [regularizedMildLocalMap_eq_shifted]
        calc
          ‖realHeatOperator t.1 t.2.1 b -
              ∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ‖ ≤
            ‖realHeatOperator t.1 t.2.1 b‖ +
              ‖∫ τ in (0 : ℝ)..T, mildShiftedStokesIntegrand F t.1 τ‖ := norm_sub_le _ _
          _ ≤ ‖b‖ + M / 2 := by
            exact add_le_add hheat (hI.trans_eq hAbel)
      have hMb : ‖b‖ + M / 2 ≤ 2 * M := by
        dsimp [M, regularizedMildLocalM]
        linarith only [norm_nonneg b]
      exact hnorm.trans hMb
  have hclosed : IsClosed S := by
    simpa [S] using regularizedMildLocalBall_isClosed T M
  have hzero : (0 : C(RegularizedMildTimeInterval T, RealVectorL2)) ∈ S := by
    change ∀ t, RegularizedMildJData (0 : RealVectorL2) ∧
      ‖(0 : RealVectorL2)‖ ≤ 2 * M
    intro t
    have hMnonneg : 0 ≤ M := by dsimp [M, regularizedMildLocalM]; positivity
    exact ⟨regularizedMildJData_zero,
      by simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hMnonneg)⟩
  let κ : NNReal := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hκ : κ < 1 := by
    exact_mod_cast (by norm_num : (1 / 2 : ℝ) < 1)
  have hLipschitz (u v : S) :
      dist (f u) (f v) ≤ κ * dist u v := by
    change dist (f u.1) (f v.1) ≤ κ * dist u.1 v.1
    rw [dist_eq_norm, dist_eq_norm]
    have hlip := regularizedMildLocalMap_sub_norm_le ρ ε hε b u.1 v.1
      (fun t => (u.2 t).2) (fun t => (v.2 t).2)
    change ‖f u.1 - f v.1‖ ≤ (1 / 2 : ℝ) * ‖u.1 - v.1‖ at hlip
    exact hlip
  have hlip : LipschitzWith κ (hmap.restrict f S S) :=
    LipschitzWith.of_dist_le_mul fun u v => by
      change dist (f u) (f v) ≤ κ * dist u v
      exact hLipschitz u v
  have hcontract : ContractingWith κ (hmap.restrict f S S) := ⟨hκ, hlip⟩
  obtain ⟨u, hu, hfixed, -, -⟩ := ContractingWith.exists_fixedPoint'
    hclosed.isComplete hmap hcontract hzero (by simp [edist_dist])
  have hmapfix : f u = u := hfixed.eq
  refine ⟨u, ?_, ?_⟩
  · intro t
    have ht := congrArg (fun w : C(RegularizedMildTimeInterval T, RealVectorL2) => w t)
      hmapfix
    simpa [f] using ht.symm.trans
      (regularizedMildLocalMap_eq_rightHandSide ρ ε hε b T hT u t)
  · intro t
    exact hu t

end CKN.Leray

end
