/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Covariance
public import LeanPool.PlanarMidpoint.TangentGeometry
public import LeanPool.PlanarMidpoint.Topology
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FinCases

/-!
# Differential rigidity of planar symmetric cubic fields

On every open preconnected planar domain, an everywhere differentiable cubic
field satisfying the quartic obstruction equation is constant. The proof
includes the exceptional cones, transitions between loci, and zero values;
no continuity of the derivative is assumed.
-/

@[expose] public section

open Set Filter

namespace PlanarMidpoint

noncomputable section

/-- Values outside the two exceptional graphs. -/
def regularLocus : Set Coeff := {c | c ≠ Q (trace c) ∧ c ≠ R (trace c)}

theorem isOpen_regularLocus : IsOpen regularLocus :=
  (isOpen_ne_fun continuous_id (continuous_Q.comp continuous_trace)).inter
    (isOpen_ne_fun continuous_id (continuous_R.comp continuous_trace))

theorem regular_obstruction_injective {c : Coeff} (hc : c ∈ regularLocus)
    (J : E →L[ℝ] Coeff) (hJ : ∀ v, obstruction c J v = 0) : J = 0 := by
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro he
    subst c
    exact hc.1 (by ext i; fin_cases i <;> simp [trace, Q, radiusSq])
  have hz : derivativeArray J ≠ 0 := by
    intro hz
    exact hne ((derivativeArray_eq_zero_iff J).mp hz)
  obtain ⟨_, hQ | hR⟩ := exceptional_of_kernel c (derivativeArray J) hc0 hz
    (kernel_of_obstruction_zero c J hJ)
  · exact hc.1 hQ
  · exact hc.2 hR

private theorem graph_or_graph {c : Coeff} (hc : c ∉ regularLocus) :
    c = Q (trace c) ∨ c = R (trace c) := by
  simp only [regularLocus, mem_ofPred_eq, not_and_or, not_not] at hc
  exact hc

private theorem trace_ne_zero_of_graph {c : Coeff} (hc : c ≠ 0)
    (h : c = Q (trace c) ∨ c = R (trace c)) : trace c ≠ 0 := by
  intro ht
  rcases h with h | h
  · rw [ht, Q_zero] at h
    exact hc h
  · rw [ht, R_zero] at h
    exact hc h

private theorem exceptional_fderiv_zero
    (Ω : Set E) (C : E → Coeff) (hΩ : IsOpen Ω)
    (hC : DifferentiableOn ℝ C Ω)
    (hpde : ∀ p ∈ Ω, ∀ h, obstruction (C p) (fderiv ℝ C p) h = 0)
    (houtside : ∀ p ∈ Ω, C p ∉ regularLocus)
    (p : E) (hp : p ∈ Ω) (hne : C p ≠ 0) : fderiv ℝ C p = 0 := by
  have hd : DifferentiableAt ℝ C p := (hC p hp).differentiableAt (hΩ.mem_nhds hp)
  have hc := hd.continuousAt
  have hb := graph_or_graph (houtside p hp)
  have ht := trace_ne_zero_of_graph hne hb
  have hlocal : ∀ᶠ q in nhds p, C q = Q (trace (C q)) ∨ C q = R (trace (C q)) := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact graph_or_graph (houtside q hq)
  let A : E →L[ℝ] E := traceCLM.comp (fderiv ℝ C p)
  have htrace : HasFDerivAt (fun q => trace (C q)) A p := by
    simpa only [Function.comp_def, traceCLM_apply] using traceCLM.hasFDerivAt.comp p hd.hasFDerivAt
  rcases hb with hQ | hR
  · have heq : C =ᶠ[nhds p] (fun q => Q (trace (C q))) :=
      eventually_eq_left_branch hc (continuous_R.continuousAt.comp
          (continuous_trace.continuousAt.comp hc))
        (Q_ne_R ht) hQ hlocal
    have hdQ := (hasFDerivAt_Q ht).comp p htrace
    have he : fderiv ℝ C p = (QDeriv (trace (C p))).comp A :=
      heq.fderiv_eq.trans hdQ.fderiv
    rw [he]
    apply Q_tangent_obstruction_zero ht A
    simpa only [← he, ← hQ] using hpde p hp
  · have hlocal' : ∀ᶠ q in nhds p, C q = R (trace (C q)) ∨ C q = Q (trace (C q)) :=
      hlocal.mono (fun _ h => h.symm)
    have heq : C =ᶠ[nhds p] (fun q => R (trace (C q))) :=
      eventually_eq_left_branch hc (continuous_Q.continuousAt.comp
          (continuous_trace.continuousAt.comp hc))
        (Ne.symm (Q_ne_R ht)) hR hlocal'
    have hdR := (hasFDerivAt_R ht).comp p htrace
    have he : fderiv ℝ C p = (RDeriv (trace (C p))).comp A :=
      heq.fderiv_eq.trans hdR.fderiv
    rw [he]
    apply R_tangent_obstruction_zero ht A
    simpa only [← he, ← hR] using hpde p hp

/-- The quartic obstruction forces a differentiable planar cubic field to be
constant on every open preconnected domain. -/
theorem planar_obstruction_rigidity
    (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (diffC : DifferentiableOn ℝ C Ω)
    (PDE : ∀ p ∈ Ω, ∀ h, obstruction (C p) (fderiv ℝ C p) h = 0) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c := by
  apply exists_is_const_of_regular_locus openΩ connectedΩ diffC regularLocus isOpen_regularLocus
  · intro p hp hregular
    exact regular_obstruction_injective hregular (fderiv ℝ C p) (PDE p hp)
  · exact exceptional_fderiv_zero Ω C openΩ diffC PDE

end
end PlanarMidpoint
