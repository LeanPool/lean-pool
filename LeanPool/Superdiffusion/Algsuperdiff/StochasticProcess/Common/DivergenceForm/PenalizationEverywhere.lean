/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationInterior
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ShiftedResolventRegularity
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.InteriorHolderConstant

/-!
# PenalizationEverywhere

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Everywhere convergence of the penalized resolvents inside the part domain.
-/

/-!
# Everywhere convergence of the penalized resolvents on the part domain

The penalization limit is available almost everywhere on the part domain `V`.
This file upgrades it to a statement at every point of `V`, using only the
uniform interior estimate: no compactness argument is needed, because the
sequence is pointwise decreasing.

The route is: continuous representatives of the penalized resolvents on `V`
(interior estimate plus local-to-global gluing); pointwise monotonicity and
nonnegativity everywhere on `V` (almost everywhere identities between
functions continuous on the open set `V`); the pointwise infimum, which
inherits the index-free Hölder bound and is therefore continuous; and the
identification of that infimum with the continuous representative of the part
resolvent.

Nothing is asserted on the boundary of `V`.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ} {V U : Set (Vec d)}

/-- An almost everywhere inequality between two functions continuous on an
open set holds at every point of that set. -/
theorem le_of_ae_le_of_continuousOn {W : Set (Vec d)} (hW : IsOpen W)
    {p q : Vec d → ℝ} (hp : ContinuousOn p W) (hq : ContinuousOn q W)
    (h : ∀ᵐ x ∂volume.restrict W, p x ≤ q x) : ∀ x ∈ W, p x ≤ q x := by
  have hcont : ContinuousOn (fun x => max (p x - q x) 0) W :=
    continuous_max.comp_continuousOn ((hp.sub hq).prodMk continuousOn_const)
  have hae : (fun x => max (p x - q x) 0) =ᵐ[volume.restrict W] fun _ => (0 : ℝ) := by
    filter_upwards [h] with x hx
    exact max_eq_right (by linarith only [hx])
  have heq := eqOn_of_continuousOn_of_ae_eq hW hcont continuousOn_const hae
  intro x hx
  have hx' : max (p x - q x) 0 = 0 := heq hx
  have hle := le_max_left (p x - q x) 0
  rw [hx'] at hle
  linarith only [hle]

/-! ## The quantitative witness for the penalized family -/

open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing in
/-- **The freezing route.**  Inside the part domain the penalization potential
vanishes, so the penalized solution satisfies the unpenalized shifted equation
there and the uniform energy bound supplies the index-free gradient budget.
Freezing at the point then gives one radius and one constant for the whole
sequence, with no restriction on the size of the skew part. -/
theorem hasLocalHolderPenalizedResolvents_continuousCoeff [NeZero d]
    (hd : 2 ≤ d) (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpen V) (hVU : V ⊆ U) {nu : ℝ} (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) U)
    {lam Lam : ℝ} (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam U a) :
    HasLocalHolderPenalizedResolvents a hU hV hlam hEll (1 / 2 : ℝ) nu⁻¹ := by
  intro mu hmu f M hM hfM x hx
  obtain ⟨s, hs, hsV, hbound⟩ :=
    exists_frozenRadius_holder_of_continuousCoeff hd hV hnu hsymm
      (hcont.mono hVU) hx
  have hsub : euclideanBall x (s / 2) ⊆ euclideanBall x s :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith only [hs])
  refine ⟨s / 2, half_pos hs, hsub.trans hsV, ?_⟩
  intro n
  obtain ⟨z, g, hzvalue, hgmem, hgsize, hgradsize, hzeq⟩ :=
    exists_interior_equation_penalized_with_gradient a hU hV hVU hmu hlam hEll
      f hM hfM n (isOpen_euclideanBall x s) hsV
  obtain ⟨v, hvcont, hvae, hvholder⟩ :=
    hbound ((min mu lam)⁻¹ * ‖f‖) M z g hgmem hgsize hgradsize hzeq
  refine ⟨v, hvcont, ?_, hvholder⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hvae,
    ae_restrict_of_ae_restrict_of_subset hsub hzvalue] with y h1 h2
  rw [h1, h2]

/-- **Everywhere penalization limit on the part domain.**  The penalized
resolvents have continuous representatives on `V` that decrease pointwise and
converge, at every point of `V`, to the continuous representative of the part
resolvent; the pointwise infimum is that representative.  The index-free
Hölder constant of the quantitative witness is what makes the infimum
continuous.  The limit's own representative is not produced here: it is the one
named by `hRegV`, at the restricted datum, and the content of the theorem is
the monotone pointwise convergence to it.  Nothing is asserted on the boundary
of `V`. -/
theorem exists_penalization_everywhere_limit_reg [NeZero d]
    (a : CoeffField d) (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    (hU : IsOpenBoundedConvexDomain U) (hVU : V ⊆ U)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {alpha B : ℝ} (halpha0 : 0 < alpha)
    (hRegPen : HasLocalHolderPenalizedResolvents a hU hV.isOpen hlam hEll
      alpha B)
    (hRegV : HasContinuousShiftedResolvents a hlam
      (hEll.mono hV.isOpen.measurableSet hVU))
    (f : ScalarL2 U) (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x)
    {M : ℝ} (hM : 0 ≤ M) (hfM : ∀ᵐ x ∂volumeMeasureOn U, |f x| ≤ M) :
    ∃ rep : ℕ → Vec d → ℝ, ∃ limit : Vec d → ℝ,
      (∀ n, ContinuousOn (rep n) V) ∧ ContinuousOn limit V ∧
      (∀ n, rep n =ᵐ[volumeMeasureOn V]
        penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f) ∧
      limit =ᵐ[volumeMeasureOn V] alphaShiftedResolvent a hα hlam
        (hEll.mono hV.isOpen.measurableSet hVU)
        (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) ∧
      (∀ x ∈ V, ∀ n, rep (n + 1) x ≤ rep n x) ∧
      (∀ x ∈ V, Tendsto (fun n => rep n x) atTop (nhds (limit x))) ∧
      (∀ x ∈ V, (⨅ n, rep n x) = limit x) := by
  -- (a) continuous representatives of the penalized resolvents
  have hstep : ∀ n : ℕ, ∃ w : Vec d → ℝ, ContinuousOn w V ∧
      w =ᵐ[volume.restrict V]
        (penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f :
          Vec d → ℝ) := by
    intro n
    refine exists_continuousOn_representative_of_local hV.isOpen _ ?_
    intro x hx
    obtain ⟨r, hr, hrV, hn⟩ := hRegPen hα f hM hfM x hx
    obtain ⟨v, hvcont, hvae, -⟩ := hn n
    exact ⟨r, hr, hrV, v, hvcont, hvae⟩
  choose rep hrepcont hrepae using hstep
  -- the continuous representative of the part resolvent
  have hfV : ∀ᵐ x ∂volumeMeasureOn V,
      |restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f x| ≤ M := by
    filter_upwards [restrictScalarL2ToPart_coeFn hV.isOpen.measurableSet
        hU.isOpen.measurableSet hVU f,
      ae_restrict_of_ae_restrict_of_subset hVU hfM] with x h1 h2
    rw [h1]
    exact h2
  obtain ⟨limit, hlimitcont, hlimitae⟩ :=
    hRegV hα (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f) hM hfV
  -- (b) pointwise monotonicity on `V`
  have hmono : ∀ x ∈ V, ∀ n, rep (n + 1) x ≤ rep n x := by
    intro x hx n
    refine le_of_ae_le_of_continuousOn hV.isOpen (hrepcont (n + 1)) (hrepcont n)
      ?_ x hx
    filter_upwards [hrepae (n + 1), hrepae n,
      ae_restrict_of_ae_restrict_of_subset hVU
        (penalizedResolvent_antitone_ae a hU hV hα hlam hEll f
          (by filter_upwards [hf] with y hy using hy) n (n + 1)
          (Nat.le_succ n))] with y h1 h2 h3
    rw [h1, h2]
    exact h3
  -- (c) pointwise nonnegativity on `V`
  have hnonneg : ∀ x ∈ V, ∀ n, 0 ≤ rep n x := by
    intro x hx n
    refine le_of_ae_le_of_continuousOn hV.isOpen continuousOn_const
      (hrepcont n) ?_ x hx
    filter_upwards [hrepae n,
      ae_restrict_of_ae_restrict_of_subset hVU
        (penalizedResolvent_nonneg_ae a hU hV hα hlam hEll f hf n)] with y h1 h2
    rw [h1]
    exact h2
  have hbdd : ∀ x ∈ V, BddBelow (Set.range fun n => rep n x) := by
    intro x hx
    exact ⟨0, by rintro _ ⟨n, rfl⟩; exact hnonneg x hx n⟩
  have hantitone : ∀ x ∈ V, Antitone fun n => rep n x := fun x hx =>
    antitone_nat_of_succ_le fun n => hmono x hx n
  -- (d) the pointwise infimum is continuous on `V`
  have hinfcont : ContinuousOn (fun x => ⨅ n, rep n x) V := by
    intro x₀ hx₀
    obtain ⟨r, hr, hballV, hn⟩ := hRegPen hα f hM hfM x₀ hx₀
    have hholder : ∀ n, EuclideanHolderBoundOn (euclideanBall x₀ r) alpha
        (penalizationInteriorHolderConstant d alpha r
          ((min α lam)⁻¹ * ‖f‖) (B * M)) (rep n) := by
      intro n
      obtain ⟨v, hvcont, hvae, hvholder⟩ := hn n
      have heq : Set.EqOn (rep n) v (euclideanBall x₀ r) := by
        refine eqOn_of_continuousOn_of_ae_eq (isOpen_euclideanBall x₀ r)
          ((hrepcont n).mono hballV) hvcont ?_
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hballV (hrepae n),
          hvae] with y h1 h2
        rw [h1, h2]
      intro y hy z hz
      rw [heq hy, heq hz]
      exact hvholder y hy z hz
    have hinf := euclideanHolderBoundOn_iInf
      (fun x hx => hbdd x (hballV hx)) hholder
    have hcont := continuousOn_of_euclideanHolderBoundOn halpha0 hinf
    exact (hcont.continuousAt
      ((isOpen_euclideanBall x₀ r).mem_nhds
        (center_mem_euclideanBall x₀ hr))).continuousWithinAt
  -- (e) identification of the infimum with the part representative
  have haeAll : ∀ᵐ x ∂volumeMeasureOn V, ∀ n,
      rep n x = penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f x :=
    (ae_all_iff).2 hrepae
  have hinfae : (fun x => ⨅ n, rep n x) =ᵐ[volume.restrict V] limit := by
    filter_upwards [haeAll,
      iInf_penalizedResolvent_eq_part_ae a hV hVne hU hVU hα hlam hEll f hf,
      hlimitae] with x h1 h2 h3
    have hrewrite : (⨅ n, rep n x) =
        ⨅ n, (penalizedResolvent a hU.isOpen hV.isOpen hα hlam hEll n f :
          Vec d → ℝ) x := by
      exact iInf_congr fun n => h1 n
    rw [hrewrite, h2, ← h3]
  have hinfEq : Set.EqOn (fun x => ⨅ n, rep n x) limit V :=
    eqOn_of_continuousOn_of_ae_eq hV.isOpen hinfcont hlimitcont hinfae
  refine ⟨rep, limit, hrepcont, hlimitcont, hrepae, hlimitae, hmono, ?_, ?_⟩
  · intro x hx
    have h := tendsto_atTop_ciInf (hantitone x hx) (hbdd x hx)
    rw [show (⨅ n, rep n x) = limit x from hinfEq hx] at h
    exact h
  · intro x hx
    exact hinfEq hx

end

end DivergenceFormProcess.Form
