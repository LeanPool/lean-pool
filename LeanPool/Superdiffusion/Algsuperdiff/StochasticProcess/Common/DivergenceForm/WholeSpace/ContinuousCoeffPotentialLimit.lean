/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffPotentialResolvent

/-!
# ContinuousCoeffPotentialLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Limits of potential-resolvent representatives

A fixed bounded nonnegative potential can be moved into the forcing term.
This reduces pointwise convergence of its continuous resolvent
representatives to the continuous-coefficient limit theorem for the
zero-potential resolvent.  The continuous skew part may have arbitrary size.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Continuous representatives of a fixed-potential resolvent converge
pointwise when the data converge in `L²` and the effective zero-potential
forcings have a common pointwise bound. -/
theorem tendsto_potentialRepresentative_of_tendsto_norm_continuousCoeff
    [NeZero d] (a : CoeffField d) (hU : IsOpenBoundedConvexDomain U)
    {alpha nu Lam C : ℝ} (halpha : 0 < alpha) (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lam U a)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    (hd : 2 ≤ d) (q : Vec d → ℝ)
    (hq : IsBoundedNonnegativePotential U q C)
    {F : ℕ → ScalarL2 U} {Fl : ScalarL2 U} {M : ℝ}
    (hM : 0 ≤ M)
    (hEffBound : ∀ k, ∀ᵐ y ∂volumeMeasureOn U,
      |(F k - potentialMul q hq
          (potentialResolvent a halpha hnu hEll q hq (F k))) y -
        (Fl - potentialMul q hq
          (potentialResolvent a halpha hnu hEll q hq Fl)) y| ≤ M)
    (hL2 : Tendsto (fun k ↦ ‖F k - Fl‖) atTop (nhds 0))
    {wk : ℕ → Vec d → ℝ} {w : Vec d → ℝ}
    (hwkcont : ∀ k, ContinuousOn (wk k) U)
    (hwkae : ∀ k, wk k =ᵐ[volumeMeasureOn U]
      potentialResolvent a halpha hnu hEll q hq (F k))
    (hwcont : ContinuousOn w U)
    (hwae : w =ᵐ[volumeMeasureOn U]
      potentialResolvent a halpha hnu hEll q hq Fl)
    {x : Vec d} (hx : x ∈ U) :
    Tendsto (fun k ↦ wk k x) atTop (nhds (w x)) := by
  let P : ScalarL2 U →L[ℝ] ScalarL2 U :=
    potentialResolvent a halpha hnu hEll q hq
  let Q : ScalarL2 U →L[ℝ] ScalarL2 U := potentialMul q hq
  let G : ℕ → ScalarL2 U := fun k ↦ F k - Q (P (F k))
  let Gl : ScalarL2 U := Fl - Q (P Fl)
  have hF : Tendsto F atTop (nhds Fl) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hL2
  have hPF : Tendsto (fun k ↦ P (F k)) atTop (nhds (P Fl)) :=
    P.continuous.continuousAt.tendsto.comp hF
  have hQPF : Tendsto (fun k ↦ Q (P (F k))) atTop (nhds (Q (P Fl))) :=
    Q.continuous.continuousAt.tendsto.comp hPF
  have hG : Tendsto G atTop (nhds Gl) := hF.sub hQPF
  have hGL2 : Tendsto (fun k ↦ ‖G k - Gl‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hG
  have hwkShift : ∀ k, wk k =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a halpha hnu hEll (G k) := by
    intro k
    have hid := potentialResolvent_perturbation_identity a halpha hnu hEll
      q hq (F k)
    rw [← map_sub] at hid
    filter_upwards [hwkae k] with y hy
    rw [hy, hid]
  have hwShift : w =ᵐ[volumeMeasureOn U]
      alphaShiftedResolvent a halpha hnu hEll Gl := by
    have hid := potentialResolvent_perturbation_identity a halpha hnu hEll
      q hq Fl
    rw [← map_sub] at hid
    filter_upwards [hwae] with y hy
    rw [hy, hid]
  have hEffBound' : ∀ k, ∀ᵐ y ∂volumeMeasureOn U,
      |G k y - Gl y| ≤ M := by
    simpa only [G, Gl, P, Q] using hEffBound
  exact tendsto_representative_of_tendsto_norm_continuousCoeff a hU
    halpha hnu hEll hsymm hcont hd (F := G) (Fl := Gl) hM hEffBound'
    hGL2 hwkcont hwkShift hwcont hwShift hx

end

end DivergenceFormProcess.Form
