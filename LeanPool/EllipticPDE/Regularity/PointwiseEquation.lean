/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.ClassicalSolvability
public import LeanPool.EllipticPDE.Extension.GlobalApproximation


/-!
# Pointwise equation of a smooth representative

A weak solution with a representative that is twice continuously differentiable on an open
subset of the domain satisfies the equation there, almost everywhere and in the classical
divergence form
`-∑ᵢⱼ ∂ⱼ(aᵢⱼ ∂ᵢu) + ∑ᵢ bᵢ ∂ᵢu + c u = f`,
the diffusion being `C¹`. This is the step the interior theory leaves to the fundamental lemma
of the calculus of variations: the weak formulation tested against a function supported in the
open set, integrated by parts once more with the classical derivatives of the representative in
place of the weak ones, says that the residual of the equation integrates to zero against every
test function, so it vanishes almost everywhere.

Two identifications feed the argument. The classical gradient of a `C¹` function on an open
set is a weak gradient there, by the integration by parts a test function's compact support
allows, and the weak gradient on an open set is unique, so the gradient coordinates of the
solution agree almost everywhere with the classical partials of the representative on every
ball whose closure lies in the set, and a countable subcover of the set by such balls makes
that agreement hold on the whole set.

## Main declarations

* `EllipticPdes.Regularity.hasWeakGradOn_of_contDiffOn`: the classical gradient of a `C¹`
  function on an open set is a weak gradient there.
* `EllipticPdes.Regularity.ae_restrict_of_forall_closedBall_subset`: a property true almost
  everywhere on every ball whose closure lies in an open set is true almost everywhere on it.
* `EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn`: the pointwise equation.
* `EllipticPdes.Regularity.exists_weakSolution_interior_classical`: solvability with a smooth
  interior representative satisfying the equation there.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Lemma I.2.4 (p. 3);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.1.2 (pp. 313–315) and §6.3.1
Theorem 3 (p. 334).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev
open EllipticPdes.Embedding (HasWeakGradOn hasWeakGradOn_unique_ae integrableOn_mul_bounded)
open EllipticPdes.Extension (hasWeakGradOn_of_mem_W12)

variable {d : ℕ}

/-! ### Two measure-theoretic lemmas -/

/-- A function continuous on an open set and vanishing off a compact subset of it is
integrable on the whole space. -/
theorem integrable_of_continuousOn_of_eq_zero_off_compact {W K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hKW : K ⊆ W) {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : ContinuousOn F W) (hFK : ∀ x, x ∉ K → F x = 0) : Integrable F volume :=
  ((hF.mono hKW).integrableOn_compact hK).integrable_of_forall_notMem_eq_zero hFK

/-- **From balls to the open set.** A property true almost everywhere on every ball whose
closure lies in an open set is true almost everywhere on the set, by a countable subcover. -/
theorem ae_restrict_of_forall_closedBall_subset {W : Set (EuclideanSpace ℝ (Fin d))}
    (hW : IsOpen W) {p : EuclideanSpace ℝ (Fin d) → Prop}
    (h : ∀ x ∈ W, ∀ r : ℝ, 0 < r → closedBall x r ⊆ W →
      ∀ᵐ y ∂(volume.restrict (ball x r)), p y) :
    ∀ᵐ y ∂(volume.restrict W), p y := by
  classical
  have key : ∀ x, x ∈ W → ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ W := by
    intro x hx
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x hx
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  choose! r hr hrW using key
  obtain ⟨t, htW, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (r x)) (s := W) fun x hx =>
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr x hx))
  refine ae_restrict_of_ae_restrict_of_subset hcover ?_
  rw [ae_restrict_biUnion_iff _ htc]
  intro x hx
  exact h x (htW hx) (r x) (hr x (htW hx)) (hrW x (htW hx))

/-! ### The classical gradient as a weak gradient -/

/-- **Classical gradient of a `C¹` function on an open set is a weak gradient there.** A test
function supported in the set has compact support, so the integration by parts has no boundary
term, and the function need only be differentiable on that support. -/
theorem hasWeakGradOn_of_contDiffOn {W : Set (EuclideanSpace ℝ (Fin d))} (hW : IsOpen W)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hv : ContDiffOn ℝ 1 v W) :
    HasWeakGradOn W v fun k => partialD k v := by
  intro φ hφc hφcs hφW k
  have hvc : ContinuousOn v W := hv.continuousOn
  have hfd : ContinuousOn (partialD k v) W :=
    (hv.continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply continuousOn_const
  have hφcont : Continuous φ := hφc.continuous
  have hdφ : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hzero1 : ∀ x, x ∉ tsupport φ → v x * partialD k φ x = 0 := fun x hx => by
    rw [show partialD k φ x = 0 from image_eq_zero_of_notMem_tsupport
      (fun hc => hx (tsupport_partialD_subset k φ hc)), mul_zero]
  have hzero2 : ∀ x, x ∉ tsupport φ → partialD k v x * φ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hzero3 : ∀ x, x ∉ tsupport φ → v x * φ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero1 x fun hc => hx (hφW hc)),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero2 x fun hc => hx (hφW hc))]
  simp only [partialD]
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
      (hfd.mul hφcont.continuousOn) hzero2
  · exact integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
      (hvc.mul hdφ.continuousOn) hzero1
  · exact integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
      (hvc.mul hφcont.continuousOn) hzero3
  · intro x hx
    exact (hv.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds (hφW hx))
  · intro x _
    exact (hφc.differentiable (by simp)).differentiableAt

/-! ### The pointwise equation -/

/-- **Pointwise equation of a smooth representative.** A weak solution of the Dirichlet
problem whose function coordinate has a representative that is `C²` on an open subset of the
domain satisfies the equation there almost everywhere, in the classical divergence form, the
diffusion being `C¹`. The weak gradient of the solution on the open set is the classical
gradient of the representative, the weak formulation tested against a function supported
there is integrated by parts once more, and the fundamental lemma of the calculus of variations
(Guo Lemma I.2.4) makes the residual vanish almost everywhere. -/
theorem weakSolution_ae_eq_of_contDiffOn (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    {W : Set (EuclideanSpace ℝ (Fin d))} (hWo : IsOpen W) (hWΩ : W ⊆ Ω)
    {u' : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu' : u' =ᵐ[volume.restrict W] fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
    (hsm : ContDiffOn ℝ 2 u' W) :
    ∀ᵐ x ∂volume, x ∈ W →
      -(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
        + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x = f x := by
  classical
  have hWm : MeasurableSet W := hWo.measurableSet
  -- regularity of the pieces on the open set
  have hu'c : ContinuousOn u' W := hsm.continuousOn
  have hgrad1 : ∀ i, ContDiffOn ℝ 1 (partialD i u') W := fun i =>
    (hsm.fderiv_of_isOpen hWo (by norm_num)).clm_apply contDiffOn_const
  have hgradc : ∀ i, ContinuousOn (partialD i u') W := fun i => (hgrad1 i).continuousOn
  have hprod1 : ∀ i j, ContDiffOn ℝ 1 (fun y => Op.a y i j * partialD i u' y) W := fun i j =>
    (hA1.contDiff i j).contDiffOn.mul (hgrad1 i)
  have hprodc : ∀ i j, ContinuousOn (fun y => Op.a y i j * partialD i u' y) W := fun i j =>
    (hprod1 i j).continuousOn
  have hdivc : ∀ i j, ContinuousOn (partialD j fun y => Op.a y i j * partialD i u' y) W :=
    fun i j =>
      ((hprod1 i j).continuousOn_fderiv_of_isOpen hWo le_rfl).clm_apply continuousOn_const
  -- the weak gradient of the solution is the classical gradient of the representative
  have hweak : HasWeakGradOn W (fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
      (fun i x => ((u : H1amb Ω) i.succ : L2D Ω) x) :=
    (hasWeakGradOn_of_mem_W12 (H01_le_W12 Ω u.2)).mono hWΩ
  have hclass : HasWeakGradOn W (fun x => ((u : H1amb Ω) 0 : L2D Ω) x)
      (fun i => partialD i u') :=
    (hasWeakGradOn_of_contDiffOn hWo (hsm.of_le one_le_two)).congr_ae hu' fun _ =>
      EventuallyEq.rfl
  have hgrad_eq : ∀ i, (fun x => ((u : H1amb Ω) i.succ : L2D Ω) x)
      =ᵐ[volume.restrict W] partialD i u' := by
    intro i
    refine ae_restrict_of_forall_closedBall_subset hWo fun x hx r hr hrW => ?_
    have hball : ball x r ⊆ W := ball_subset_closedBall.trans hrW
    refine hasWeakGradOn_unique_ae isOpen_ball measurableSet_ball ?_ ?_ (hweak.mono hball)
      (hclass.mono hball) i
    · intro k
      have : IsFiniteMeasure (volume.restrict (ball x r)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
      exact ((Lp.memLp ((u : H1amb Ω) k.succ)).mono_measure
        (Measure.restrict_mono (hball.trans hWΩ) le_rfl)).integrable one_le_two
    · intro k
      exact (((hgradc k).mono hrW).integrableOn_compact (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall
  -- the restriction of the extension by zero is the class on the set
  have hres : ∀ g : L2D Ω,
      (restrictL2 (Ω := W) (extendL2 hΩm g) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict W] (g : EuclideanSpace ℝ (Fin d) → ℝ) := by
    intro g
    filter_upwards [coeFn_restrictL2 (Ω := W) (extendL2 hΩm g),
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hWm] with x h1 h2 h3
    rw [h1, h2, Set.indicator_of_mem (hWΩ h3)]
  have hfK : ∀ K : Set (EuclideanSpace ℝ (Fin d)), K ⊆ W → IsCompact K →
      IntegrableOn (f : EuclideanSpace ℝ (Fin d) → ℝ) K volume := by
    intro K hKW hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    exact ((Lp.memLp f).mono_measure (Measure.restrict_mono (hKW.trans hWΩ) le_rfl)).integrable
      one_le_two
  -- the residual
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
    -(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
      + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x - f x with hF
  have hbm : ∀ i, AEStronglyMeasurable (fun x => Op.b x i) (volume.restrict W) :=
    fun i => (Op.b_meas i).aestronglyMeasurable
  have hbb : ∀ i, ∀ᵐ x ∂(volume.restrict W), ‖Op.b x i‖ ≤ Op.Bsup := fun i =>
    ae_restrict_of_ae ((Op.b_bdd i).mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hcm : AEStronglyMeasurable Op.c (volume.restrict W) := Op.c_meas.aestronglyMeasurable
  have hcb : ∀ᵐ x ∂(volume.restrict W), ‖Op.c x‖ ≤ Op.Csup :=
    ae_restrict_of_ae (Op.c_bdd.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  -- the residual is locally integrable on the set
  have hloc : LocallyIntegrableOn F W volume := by
    rw [locallyIntegrableOn_iff hWo.isLocallyClosed]
    intro K hKW hK
    have hbm' : ∀ i, AEStronglyMeasurable (fun x => Op.b x i) (volume.restrict K) :=
      fun i => (Op.b_meas i).aestronglyMeasurable
    have hbb' : ∀ i, ∀ᵐ x ∂(volume.restrict K), ‖Op.b x i‖ ≤ Op.Bsup := fun i =>
      ae_restrict_of_ae ((Op.b_bdd i).mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
    have hcb' : ∀ᵐ x ∂(volume.restrict K), ‖Op.c x‖ ≤ Op.Csup :=
      ae_restrict_of_ae (Op.c_bdd.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
    have h1 : IntegrableOn (fun x => ∑ i, ∑ j,
        partialD j (fun y => Op.a y i j * partialD i u' y) x) K volume :=
      ((continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
        hdivc i j).mono hKW).integrableOn_compact hK
    have h2 : IntegrableOn (fun x => ∑ i, Op.b x i * partialD i u' x) K volume :=
      integrable_finsetSum _ fun i _ =>
        Integrable.bdd_mul (((hgradc i).mono hKW).integrableOn_compact hK) (hbm' i) (hbb' i)
    have h3 : IntegrableOn (fun x => Op.c x * u' x) K volume :=
      Integrable.bdd_mul ((hu'c.mono hKW).integrableOn_compact hK) Op.c_meas.aestronglyMeasurable
        hcb'
    have h4 : IntegrableOn (f : EuclideanSpace ℝ (Fin d) → ℝ) K volume := hfK K hKW hK
    exact ((h1.neg.add h2).add h3).sub h4
  -- the residual integrates to zero against every test function
  have htest : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, φ x • F x ∂volume = 0 := by
    intro φ hφc hφcs hφW
    have hφcont : Continuous φ := hφc.continuous
    have hdφ : ∀ j, Continuous (partialD j φ) := fun j =>
      (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
    have hoff : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ, ∀ x, x ∉ tsupport φ → φ x * G x = 0 :=
      fun G x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    have hoff' : ∀ G : EuclideanSpace ℝ (Fin d) → ℝ, ∀ x, x ∉ tsupport φ → G x * φ x = 0 :=
      fun G x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    -- integrability, on the set, of the test function against each piece
    have hint_div : ∀ i j, Integrable (fun x => φ x *
        partialD j (fun y => Op.a y i j * partialD i u' y) x) (volume.restrict W) :=
      fun i j => (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
        (hφcont.continuousOn.mul (hdivc i j)) (hoff _)).integrableOn
    have hint_grad : ∀ i, Integrable (fun x => φ x * partialD i u' x) (volume.restrict W) :=
      fun i => (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
        (hφcont.continuousOn.mul (hgradc i)) (hoff _)).integrableOn
    have hint_b : ∀ i, Integrable (fun x => Op.b x i * (φ x * partialD i u' x))
        (volume.restrict W) :=
      fun i => Integrable.bdd_mul (hint_grad i) (hbm i) (hbb i)
    have hint_u : Integrable (fun x => φ x * u' x) (volume.restrict W) :=
      (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
        (hφcont.continuousOn.mul hu'c) (hoff _)).integrableOn
    have hint_c : Integrable (fun x => Op.c x * (φ x * u' x)) (volume.restrict W) :=
      Integrable.bdd_mul hint_u hcm hcb
    obtain ⟨M, hM⟩ := hφcs.exists_bound_of_continuous hφcont
    have hint_f : Integrable (fun x => (f x : ℝ) * φ x) (volume.restrict W) := by
      refine IntegrableOn.of_forall_sdiff_eq_zero
        (integrableOn_mul_bounded (hfK _ hφW hφcs.isCompact) hφcont hM) hWm fun x hx => ?_
      exact hoff' _ x hx.2
    -- the localised weak formulation, read against the representative
    have hloc' := localWeakForm_of_fullBilin Op hΩm hWm hWΩ u f hu φ hφc hφcs hφW
    have e1 : ∀ i j, ∫ x in W, Op.a x i j
        * (restrictL2 (Ω := W) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * partialD j φ x
        = ∫ x in W, Op.a x i j * partialD i u' x * partialD j φ x := fun i j =>
      integral_congr_ae (by
        filter_upwards [hres ((u : H1amb Ω) i.succ), hgrad_eq i] with x h1 h2
        rw [h1, h2])
    have e2 : ∀ i, ∫ x in W, Op.b x i
        * (restrictL2 (Ω := W) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * φ x
        = ∫ x in W, Op.b x i * (φ x * partialD i u' x) := fun i =>
      integral_congr_ae (by
        filter_upwards [hres ((u : H1amb Ω) i.succ), hgrad_eq i] with x h1 h2
        rw [h1, h2]; ring)
    have e3 : ∫ x in W, Op.c x
        * (restrictL2 (Ω := W) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ) * φ x
        = ∫ x in W, Op.c x * (φ x * u' x) :=
      integral_congr_ae (by
        filter_upwards [hres ((u : H1amb Ω) 0), hu'] with x h1 h2
        rw [h1, h2]; ring)
    have e4 : ∫ x in W, (restrictL2 (Ω := W) (extendL2 hΩm f) x : ℝ) * φ x
        = ∫ x in W, (f x : ℝ) * φ x :=
      integral_congr_ae (by filter_upwards [hres f] with x h1; rw [h1])
    simp only [e1, e2, e3, e4] at hloc'
    -- integration by parts on the principal term
    have hibp : ∀ i j, ∫ x in W, Op.a x i j * partialD i u' x * partialD j φ x
        = -∫ x in W, φ x * partialD j (fun y => Op.a y i j * partialD i u' y) x := by
      intro i j
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [show partialD j φ x = 0 from image_eq_zero_of_notMem_tsupport
            (fun hc => hx (hφW (tsupport_partialD_subset j φ hc))), mul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
          hoff _ x fun hc => hx (hφW hc))]
      have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        (f := fun y => Op.a y i j * partialD i u' y) (g := φ) (v := EuclideanSpace.single j 1)
        (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
          ((hdivc i j).mul hφcont.continuousOn) (hoff' _))
        (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
          ((hprodc i j).mul (hdφ j).continuousOn) (fun x hx => by
            rw [show (fderiv ℝ φ x) (EuclideanSpace.single j 1) = 0 from
              image_eq_zero_of_notMem_tsupport (f := partialD j φ)
                (fun hc => hx (tsupport_partialD_subset j φ hc)), mul_zero]))
        (integrable_of_continuousOn_of_eq_zero_off_compact hφcs.isCompact hφW
          ((hprodc i j).mul hφcont.continuousOn) (hoff' _))
        (fun x hx => ((hprod1 i j).differentiableOn one_ne_zero).differentiableAt
          (hWo.mem_nhds (hφW hx)))
        (fun x _ => (hφc.differentiable (by simp)).differentiableAt)
      change ∫ x, (fun y => Op.a y i j * partialD i u' y) x * (fderiv ℝ φ x)
          (EuclideanSpace.single j 1)
        = -∫ x, φ x * (fderiv ℝ (fun y => Op.a y i j * partialD i u' y) x)
          (EuclideanSpace.single j 1)
      rw [key]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    simp only [hibp, Finset.sum_neg_distrib] at hloc'
    -- assemble the integral of the residual
    have hpt : ∀ x, φ x • F x = -(∑ i, ∑ j, φ x *
        partialD j (fun y => Op.a y i j * partialD i u' y) x)
        + ∑ i, Op.b x i * (φ x * partialD i u' x) + Op.c x * (φ x * u' x) - (f x : ℝ) * φ x := by
      intro x
      have h2 : ∀ i, φ x * (Op.b x i * partialD i u' x) = Op.b x i * (φ x * partialD i u' x) :=
        fun i => by ring
      simp only [hF, smul_eq_mul, mul_add, mul_sub, mul_neg, Finset.mul_sum, h2]
      ring
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) (fun x hx => by
      rw [smul_eq_mul, hoff _ x fun hc => hx (hφW hc)]) |>.symm]
    simp_rw [hpt]
    rw [integral_sub, integral_add, integral_add, integral_neg,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_div i j,
      integral_finsetSum _ fun i _ => hint_b i]
    · simp only [integral_finsetSum _ fun j _ => hint_div _ j]
      linarith [hloc']
    · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint_div i j).neg
    · exact integrable_finsetSum _ fun i _ => hint_b i
    · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        hint_div i j).neg.add (integrable_finsetSum _ fun i _ => hint_b i)
    · exact hint_c
    · exact ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        hint_div i j).neg.add (integrable_finsetSum _ fun i _ => hint_b i)).add hint_c
    · exact hint_f
  -- the fundamental lemma of the calculus of variations
  have hae := hWo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc htest
  filter_upwards [hae] with x hx hxW
  have := hx hxW
  simp only [hF] at this
  linarith

/-- **Solvability with a smooth interior representative satisfying the equation.** On a
bounded domain, for an operator with no transport term and a nonnegative zeroth-order
coefficient, whose diffusion is `C¹` and whose coefficients lie in `W^{k,∞}` at every order,
and for a datum with weak derivatives of every order bounded in `L²`, the Dirichlet problem has
a weak solution whose class has a `C^∞` representative on the interior of every compact subset
of the domain, and that representative satisfies the equation there almost everywhere. -/
theorem exists_weakSolution_interior_classical {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (hA1 : IsC1Coeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) ∧
      ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        u' =ᵐ[volume.restrict (interior V)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) ∧
          ∀ᵐ x ∂volume, x ∈ interior V →
            -(∑ i, ∑ j, partialD j (fun y => Op.a y i j * partialD i u' y) x)
              + ∑ i, Op.b x i * partialD i u' x + Op.c x * u' x = f x := by
  obtain ⟨u, hu, u', hu', hsm⟩ :=
    exists_weakSolution_interior_smooth Op hΩm hΩo hΩb hb hc hA1.toIsLipCoeff hA hbc f hf hVc hVΩ
  have hWΩ : interior V ⊆ Ω := interior_subset.trans hVΩ
  have hu'2 : u' =ᵐ[volume.restrict (interior V)] fun x => ((u : H1amb Ω) 0 : L2D Ω) x := by
    filter_upwards [hu', ae_restrict_of_ae (coeFn_extendL2 hΩm ((u : H1amb Ω) 0)),
      ae_restrict_mem isOpen_interior.measurableSet] with x h1 h2 h3
    rw [h1, h2, Set.indicator_of_mem (hWΩ h3)]
  refine ⟨u, hu, u', hu', hsm, ?_⟩
  exact weakSolution_ae_eq_of_contDiffOn Op hΩm hA1 u f hu isOpen_interior hWΩ hu'2
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))

end EllipticPdes.Regularity
