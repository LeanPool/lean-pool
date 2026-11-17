/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Caffarelli.MomentRegularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Gradient.Lipschitz
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.SecondOrder.HessianRegularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Regularity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Taylor
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Gradient
public import Mathlib.Topology.TietzeExtension
public import LeanPool.KLS.FunctionalInequalities.KLS.CEK.MomentMap
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.HessianKernel

/-!
# Moment potentials for continuous convex-body targets and the strong regular class

The continuous-target producers require only continuity of W on the compact body (or the closure
of a bounded open convex body). They yield C¹, strict convexity, a gradient homeomorphism and
the Alexandrov/viscosity equation without uniform convexity. Higher regularity remains separate.

The regular-class moment witness (`exists_regular_moment_potential`) and two extensions at the same
`u` and `L`: a
measurable everywhere left inverse of the injective gradient
(`exists_regular_moment_potential_with_inverse`, via the
given-witness adapter `measurable_inverse_gradient_of_map_gradient`) and compact-local uniform
ellipticity
(`exists_regular_moment_potential_locally_elliptic`).
-/

@[expose] public section

section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

section ContinuousTarget
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Moment-map support for the literal convex-source Lemma 2.2: no uniform convexity or
higher regularity premise. The conclusion is C¹, a gradient homeomorphism and the actual
Alexandrov/viscosity equation; C^{1,alpha}, W^{2,p} and C-infinity remain separate. -/
theorem exists_moment_potential_of_continuousOn (hn : 0 < n)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    {W : E → ℝ} (hW : ContinuousOn W K) (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧
      (∃ e : E ≃ₜ interior K, ∀ x, (e x : E) = gradient u x) ∧
      Continuous (fun x => Real.exp (-u x + W (gradient u x))) ∧
      (∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + W (gradient u x)))) ∧
      (∀ᵐ x ∂(volume : Measure E), ∃ B : Matrix (Fin n) (Fin n) ℝ,
        B.IsHermitian ∧ B.PosDef ∧ B.det = Real.exp (-u x + W (gradient u x)) ∧
        ∃ g : E, ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2) ∧
      (∀ (x : E) (ψ : E → ℝ), ContDiffAt ℝ 2 ψ x → u x = ψ x →
        (∀ᶠ y in 𝓝 x, u y ≤ ψ y) →
        Real.exp (-u x + W (gradient u x)) ≤ (hessianMatrix ψ x).det) ∧
      ∀ (x : E) (ψ : E → ℝ), ContDiffAt ℝ 2 ψ x → (hessianMatrix ψ x).PosSemidef →
        u x = ψ x → (∀ᶠ y in 𝓝 x, ψ y ≤ u y) →
        (hessianMatrix ψ x).det ≤ Real.exp (-u x + W (gradient u x)) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let w : C(K, ℝ) := ⟨fun y => W y, continuousOn_iff_continuous_domRestrict.mp hW⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed w
  have hEq : ∀ y ∈ K, F y = W y := by
    intro y hy
    exact congrArg (fun g : C(K, ℝ) => g ⟨y, hy⟩) hF
  have hDensity : (K.indicator fun y => ENNReal.ofReal (Real.exp (-W y))) =
      K.indicator fun y => ENNReal.ofReal (Real.exp (-F y)) := by
    funext y
    by_cases hy : y ∈ K
    · simp only [indicator_of_mem hy, hEq y hy]
    · simp only [indicator_of_notMem hy]
  have hμF : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun y => ENNReal.ofReal (Real.exp (-F y))) := by
    rw [hμ, hDensity]
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  let L : NNReal := ⟨R, hR.le⟩
  have hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ) := by
    rw [hμF]
    refine (ae_withDensity_iff (F.continuous.measurable.neg.exp.ennreal_ofReal.indicator
      hK.measurableSet)).2 ?_
    filter_upwards [] with y hy
    by_cases hyK : y ∈ K
    · exact hRK y hyK
    · rw [indicator_of_notMem hyK] at hy
      exact (hy rfl).elim
  obtain ⟨u, hc, hl, hnorm, hm⟩ := KLS.CEK.exists_momentMap_of_isotropic_of_ae_norm_le μ hiso L hL
  have hmF := hm.trans hμF
  have hstrict := strictConvexOn_of_map_gradient hl hc hnorm hK hKc
    (hKint.mono interior_subset) F.continuous hmF
  have hC1 := contDiff_one_of_map_gradient hl hc hnorm hK hKc hKint F.continuous hmF
  obtain ⟨e, he⟩ := Probability.MomentMeasure.exists_gradient_homeomorph_interior_of_map_gradient
    hn hl hc hnorm hC1 hK hKc hKint F.continuous hmF
  have hgradK (x : E) : gradient u x ∈ K := by
    rw [← he x]
    exact interior_subset (e x).property
  have hFg (x : E) : F (gradient u x) = W (gradient u x) := hEq _ (hgradK x)
  have hf : Continuous (fun x => Real.exp (-u x + W (gradient u x))) := by
    have h := Real.continuous_exp.comp
      (hC1.continuous.neg.add (F.continuous.comp (BakryEmery.continuous_gradient hC1)))
    change Continuous (fun x => Real.exp (-u x + F (gradient u x))) at h
    simpa only [hFg] using h
  have hMA (G : Set E) (hG : IsOpen G) : volume (subgradientImage u G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + W (gradient u x))) := by
    simpa only [hFg] using volume_subgradientImage_eq_lintegral_of_isOpen hl hc hnorm
      hK.isClosed hKc F.continuous.measurable hmF hG
  refine ⟨u, L, hstrict, hl, hnorm, hm, hC1, ⟨e, he⟩, hf, hMA,
    ae_exists_posDef_det_eq hc hf (fun x => Real.exp_pos _) hMA, ?_, ?_⟩
  · intro x ψ hψ hcontact htouch
    exact le_det_hessianMatrix_of_upper_touch hc isOpen_univ
      (fun G hG _ => hMA G hG) (mem_univ x) hf.continuousAt hψ hcontact htouch
  · intro x ψ hψ hH hcontact htouch
    exact det_hessianMatrix_le_of_lower_touch hc isOpen_univ
      (fun G hG _ => hMA G hG) (mem_univ x) hf.continuousAt (Real.exp_pos _).le
      hψ hH hcontact htouch
/-- The literal bounded open convex-body inputs of Letwin Lemma 2.2 yield a normalized finite C¹
moment potential, a gradient homeomorphism onto K and the Alexandrov/viscosity equation.
Continuity on closure K suffices here; smoothness and convexity of W are not needed for this step.
-/
theorem exists_moment_potential_of_bounded_open_convex (hn : 0 < n) {K : Set E}
    (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {W : E → ℝ} (hW : ContinuousOn W (closure K)) (μ : ProbabilityMeasure E)
    (hμ :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal),
      StrictConvexOn ℝ univ u ∧
        LipschitzWith L u ∧
          (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
            ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
              ContDiff ℝ 1 u ∧
                (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
                  Continuous (fun x => Real.exp (-u x + W (gradient u x))) ∧
                    (∀ G : Set E,
                        IsOpen G →
                          volume (subgradientImage u G) =
                            ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + W (gradient u x)))) ∧
                      (∀ᵐ x ∂(volume : Measure E),
                          ∃ B : Matrix (Fin n) (Fin n) ℝ,
                            B.IsHermitian ∧
                              B.PosDef ∧
                                B.det = Real.exp (-u x + W (gradient u x)) ∧
                                  ∃ g : E,
                                    ∀ ε > 0,
                                      ∀ᶠ y in 𝓝 x,
                                        |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2) ∧
                        (∀ (x : E) (ψ : E → ℝ),
                            ContDiffAt ℝ 2 ψ x →
                              u x = ψ x →
                                (∀ᶠ y in 𝓝 x, u y ≤ ψ y) →
                                  Real.exp (-u x + W (gradient u x)) ≤
                                    (hessianMatrix ψ x).det) ∧
                          ∀ (x : E) (ψ : E → ℝ),
                            ContDiffAt ℝ 2 ψ x →
                              (hessianMatrix ψ x).PosSemidef →
                                u x = ψ x →
                                  (∀ᶠ y in 𝓝 x, ψ y ≤ u y) →
                                    (hessianMatrix ψ x).det ≤
                                      Real.exp (-u x + W (gradient u x)) := by
  have hInt : interior (closure K) = K := by
    rw [hKc.interior_closure_eq_interior_of_nonempty_interior, hKo.interior_eq]
    simpa only [hKo.interior_eq] using hKne
  have hμcl :
    (μ : Measure E) =
      (volume : Measure E).withDensity
        ((closure K).indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
    rw [hμ]
    apply withDensity_congr_ae
    have hnull : ∀ᵐ x ∂(volume : Measure E), x ∉ frontier K :=
      measure_eq_zero_iff_ae_notMem.mp (hKc.addHaar_frontier volume)
    filter_upwards [hnull] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, indicator_of_mem (subset_closure hxK)]
    · have hxcl : x ∉ closure K := by
        intro hc
        exact hx ⟨hc, by simpa only [hKo.interior_eq] using hxK⟩
      rw [indicator_of_notMem hxK, indicator_of_notMem hxcl]
  obtain ⟨u, L, hstrict, hl, hnorm, hm, hC1, ⟨e, he⟩, hf, hMA, hae, hUpper, hLower⟩ :=
    exists_moment_potential_of_continuousOn hn hKb.isCompact_closure hKc.closure
      (by simpa only [hInt] using hKne) hW μ hμcl hiso
  exact
    ⟨u, L, hstrict, hl, hnorm, hm, hC1, ⟨e.trans (Homeomorph.setCongr hInt), he⟩, hf, hMA, hae,
      hUpper, hLower⟩

end ContinuousTarget

/--
**A.e. Hessian package at a given moment potential with Lipschitz gradient**: if a normalized convex
Lipschitz `C¹` potential `u` with `G`-Lipschitz gradient pushes `e^{-u} dx` forward by `∇u` onto
`1_K e^{-W} dx` (`K` compact convex, `W` continuous, positive dimension), then a.e. its Hessian is
positive definite, satisfies `log det ∇²u = -u + W(∇u)` and is capped by `G·Id`. The potential is
given; no convexity or smoothness of `W` is used. -/
theorem ae_hessianMatrix_posDef_log_det_of_map_gradient {n : ℕ} (hn : 0 < n)
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal} (huLip : LipschitzWith L u)
    (huconv : ConvexOn ℝ univ u)
    (hunorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hW : Continuous W)
    (hmap :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (huC1 : ContDiff ℝ 1 u) (hgradLip : LipschitzWith G (gradient u)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
          ((G : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial E := inferInstance
  let f : E → ℝ := fun x => Real.exp (-u x + W (gradient u x))
  have hgradc : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (huC1.continuous_fderiv (by norm_num))
  have hf : Continuous f := Real.continuous_exp.comp (huC1.continuous.neg.add (hW.comp hgradc))
  have hfpos : ∀ x, 0 < f x := fun x => Real.exp_pos _
  have hMA :
    ∀ O : Set E, IsOpen O → volume (subgradientImage u O) = ∫⁻ x in O, ENNReal.ofReal (f x) := by
    intro O hO
    exact
      volume_subgradientImage_eq_lintegral_of_isOpen huLip huconv hunorm hK.isClosed hKc
        hW.measurable hmap hO
  have hdiff : ∀ᵐ x ∂(volume : Measure E), DifferentiableAt ℝ (gradient u) x :=
    hgradLip.ae_differentiableAt
  have hmain :
    ∀ᵐ x ∂(volume : Measure E),
      (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = -u x + W (gradient u x) := by
    filter_upwards [hdiff] with x hx
    let T : E →L[ℝ] E := fderiv ℝ (gradient u) x
    have hT : HasFDerivAt (gradient u) T x := hx.hasFDerivAt
    have hfd : ∀ y, HasFDerivAt u (fderiv ℝ u y) y := fun y =>
      (huC1.differentiable (by norm_num) y).hasFDerivAt
    have hsub (y q : E) (hq : ∀ w, u y + ⟪q, w - y⟫ ≤ u w) : q = gradient u y := by
      have hm : IsLocalMin (fun z => u z - (InnerProductSpace.toDual ℝ E q) z) y := by
        filter_upwards [] with z
        change
          u y - (InnerProductSpace.toDual ℝ E q) y ≤ u z - (InnerProductSpace.toDual ℝ E q) z
        simp only [InnerProductSpace.toDual_apply_apply]
        have hz := hq z
        rw [inner_sub_right] at hz
        linarith
      have hz :=
        hm.hasFDerivAt_eq_zero ((hfd y).sub (InnerProductSpace.toDual ℝ E q).hasFDerivAt)
      have hdu : fderiv ℝ u y = (InnerProductSpace.toDual ℝ E) (gradient u y) :=
        (toDual_gradient (f := u) (x := y)).symm
      rw [hdu] at hz
      exact ((InnerProductSpace.toDual ℝ E).injective (sub_eq_zero.mp hz)).symm
    have hexp :
      ∀ ε > 0,
        ∀ᶠ y in 𝓝 x,
          ∀ q : E,
            (∀ w, u y + ⟪q, w - y⟫ ≤ u w) → ‖q - gradient u x - T (y - x)‖ ≤ ε * ‖y - x‖ := by
      intro ε hε
      have hlittle := hT.isLittleO
      filter_upwards [hlittle.bound hε] with y hy q hq
      have hqeq := hsub y q hq
      simpa only [hqeq] using hy
    have hquad :
      ∀ ε > 0,
        ∀ᶠ y in 𝓝 x,
          |u y - u x - ⟪gradient u x, y - x⟫ - 1 / 2 * ⟪T (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 :=
      fun ε hε => eventually_abs_sub_quadratic_le_of_subgradient_expansion huconv hexp ε hε
    have hmat := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient huC1 hx
    have hquad' :
      ∀ ε > 0,
        ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt (hessianMatrix u x) x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
      intro ε hε
      filter_upwards [hquad ε hε] with y hy
      rw [quadraticAt, hmat]
      change
        |u y - (u x + ⟪gradient u x, y - x⟫ + 1 / 2 * ⟪y - x, T (y - x)⟫)| ≤ ε * ‖y - x‖ ^ 2
      rw [real_inner_comm (T (y - x)) (y - x)]
      simpa only [sub_add_eq_sub_sub] using hy
    have hres :=
      posDef_and_det_eq_of_quadratic_expansion huconv isOpen_univ (fun O hO _ => hMA O hO)
        (mem_univ x) hf.continuousAt (hfpos x)
        (hessianMatrix_isHermitian_of_differentiableAt_gradient huC1 hx) hquad'
    refine ⟨hres.1, ?_⟩
    calc
      Real.log (hessianMatrix u x).det = Real.log (f x) := by rw [hres.2]
      _ = -u x + W (gradient u x) := by simp [f]
  filter_upwards [hmain, hdiff] with x hx hxd
  refine ⟨hx.1, hx.2, ?_⟩
  let T : E →L[ℝ] E := fderiv ℝ (gradient u) x
  have hTnorm : ‖T‖ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ hgradLip (x₀ := x)
  have hmat := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient huC1 hxd
  have hH : (hessianMatrix u x).IsHermitian :=
    hessianMatrix_isHermitian_of_differentiableAt_gradient huC1 hxd
  have hsym : T.toLinearMap.IsSymmetric := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    rw [hmat] at hs
    exact hs
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hone : Matrix.toLin b.toBasis b.toBasis (1 : Matrix (Fin n) (Fin n) ℝ) = LinearMap.id :=
    Matrix.toLin_one _
  have hop :
    Matrix.toEuclideanLin ((G : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x) =
      (G : ℝ) • LinearMap.id - T.toLinearMap := by
    have hmat' := hmat
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at hmat'
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, map_sub, map_smul, hone, hmat']
  rw [← Matrix.isPositive_toEuclideanLin_iff, hop]
  constructor
  · intro v w
    change ⟪(G : ℝ) • v - T v, w⟫ = ⟪v, (G : ℝ) • w - T w⟫
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    have hsw : ⟪T v, w⟫ = ⟪v, T w⟫ := hsym v w
    rw [hsw]
  · intro v
    change 0 ≤ ⟪(G : ℝ) • v - T v, v⟫
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hv := T.le_opNorm v
    have hv' : ‖T v‖ ≤ (G : ℝ) * ‖v‖ :=
      hv.trans (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg v))
    have hi := real_inner_le_norm (T v) v
    have hq := mul_le_mul_of_nonneg_right hv' (norm_nonneg v)
    nlinarith




/-- A regular-class isotropic law has a convex Lipschitz C1 moment potential with
16/kappa-Lipschitz gradient and the a.e. Hessian/log-det package. -/
theorem exists_regular_moment_potential {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  obtain ⟨u, L, hstrict, huLip, hunorm, humap, huC1, _he, _hf, _hMA, _hae, _hUpper, _hLower⟩ :=
    exists_moment_potential_of_continuousOn hn hK hKc hKint hW.continuous.continuousOn μ hμ hiso
  have huconv := hstrict.convexOn
  have hmap := humap.trans hμ
  have hgradLip : LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) :=
    lipschitzWith_gradient_of_map_gradient huLip huconv hunorm hK hKc
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hκ hstrong hmap huC1
  have hdata := ae_hessianMatrix_posDef_log_det_of_map_gradient hn huLip huconv hunorm hK hKc
    hW.continuous hmap huC1 hgradLip
  have hcap : ((Real.toNNReal (16 / κ) : NNReal) : ℝ) = 16 / κ :=
    Real.coe_toNNReal _ (by positivity)
  refine ⟨u, L, huconv, huLip, hunorm, humap, huC1, hgradLip, ?_⟩
  simpa only [hcap] using hdata



end FunctionalInequalities.Analysis

section RegularMomentInverseEllipticity

open MeasureTheory Set
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/--
**Gradient inverse at a given moment witness**: if a normalized convex Lipschitz `C¹` potential `u`
pushes `e^{-u} dx`
forward by `∇u` onto `1_K e^{-W} dx` (`K` compact convex nonempty, `W` continuous, positive
dimension), then `∇u` is
injective and has a measurable everywhere left inverse. Applies to the given `u`; no new potential
is chosen. -/
theorem measurable_inverse_gradient_of_map_gradient {n : ℕ} (hn : 0 < n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hC1 : ContDiff ℝ 1 u) {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) {W : EuclideanSpace ℝ (Fin n) → ℝ}
    (hW : Continuous W)
    (hmap :
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) :
    Function.Injective (gradient u) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Measurable Ψ ∧ Function.LeftInverse Ψ (gradient u) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hstrict := strictConvexOn_of_map_gradient hLip hc hnorm hK hKc hKne hW hmap
  have hinj := injective_gradient_of_strictConvexOn (hC1.differentiable (by norm_num)) hstrict
  exact ⟨hinj, Probability.Stein.exists_measurable_leftInverse_gradient_of_injective hC1 hinj⟩

/--
The actual regular moment potential of `exists_regular_moment_potential`, with all of its fields at
the same `u` and `L`,
has an injective gradient with a measurable everywhere left inverse. No `C²`, surjectivity or
smoothness claim. -/
theorem exists_regular_moment_potential_with_inverse {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ :
      (μ : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧
        LipschitzWith L u ∧
          (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
                (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
              ContDiff ℝ 1 u ∧
                LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
                  (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                      (hessianMatrix u x).PosDef ∧
                        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
                          ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
                              hessianMatrix u x).PosSemidef) ∧
                    Function.Injective (gradient u) ∧
                      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
                        Measurable Ψ ∧ Function.LeftInverse Ψ (gradient u) := by
  obtain ⟨u, L, hc, hl, hnorm, hm, hC1, hG, hdata⟩ :=
    exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hInv :=
    measurable_inverse_gradient_of_map_gradient hn hl hc hnorm hC1 hK hKc
      (hKint.mono interior_subset) hW.continuous (hm.trans hμ)
  exact ⟨u, L, hc, hl, hnorm, hm, hC1, hG, hdata, hInv⟩

/--
The actual regular moment potential of `exists_regular_moment_potential`, with all of its fields at
the same `u` and `L`,
is compact-locally uniformly elliptic: on every compact `S` its Hessian is a.e. at least `δ·Id` for
some `δ > 0` depending
on `S` (the upper bound `16/κ` is already a field). Support for interior regularity; no `C²`,
smoothness or everywhere
positive definiteness claim. -/
theorem exists_regular_moment_potential_locally_elliptic {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ :
      (μ : Measure (EuclideanSpace ℝ (Fin n))) =
        (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧
        LipschitzWith L u ∧
          (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
                (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
              ContDiff ℝ 1 u ∧
                LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
                  (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                      (hessianMatrix u x).PosDef ∧
                        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
                          ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
                              hessianMatrix u x).PosSemidef) ∧
                    ∀ S : Set (EuclideanSpace ℝ (Fin n)),
                      IsCompact S →
                        ∃ δ : ℝ,
                          0 < δ ∧
                            ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
                              (hessianMatrix u x -
                                  δ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  obtain ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hgradLip, hdata⟩ :=
    exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hgradLip, hdata, ?_⟩
  have hgradc : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hC1.continuous_fderiv (by norm_num))
  have hg : Continuous (fun x => -u x + W (gradient u x)) :=
    hC1.continuous.neg.add (hW.continuous.comp hgradc)
  intro S hS
  exact
    ae_posSemidef_hessianMatrix_sub_of_log_det hn (div_pos (by norm_num : (0 : ℝ) < 16) hκ) hg
      hdata hS

end FunctionalInequalities.Analysis

end RegularMomentInverseEllipticity
