/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Finish.AxialRecovery
public import LeanPool.FastDynamo.Global.SpectralCircleGrowthFloor
public import LeanPool.FastDynamo.Operator.HorizontalSectorBasic

/-!
# Eigenvalue extraction for the horizontal two-component torus operator

This module is the last step of Section 7 of the paper: the
eigenvalue extraction half of Proposition 7.1 (`prop:global-spectral-transfer`),
carried out for the **horizontal** two-component torus operator `A_{ε,K}` of
`eq:torus-sector` rather than for the three-component `reducedInductionOperator`.

The paper's proof of `prop:global-spectral-transfer` reads:

> Lemmas `lem:global-contour-resolvent` and `lem:global-riesz-nonzero` give the
> contour resolvent and the non-zero Riesz projection.  By Lemma
> `lem:torus-sector-basic`, the resolvent is compact.  Thus the spectrum inside
> `Γ_τ` consists of isolated eigenvalues of finite algebraic multiplicity, and
> the non-zero projection shows that this spectrum is nonempty.  Every eigenvalue in
> this region has real part at least `g_*`, since translation by `−iτ` preserves real
> parts.

(The Lean statements below extract a single eigenpair, which is the stronger reading of the
last sentence.)

Everything below is stated in hypothesis form: the two quantitative inputs, the contour
resolvent and the nonvanishing of the projection, appear only as hypotheses
(`h : HasResolventOn …` and `h.rieszProjection ≠ 0`).

## What is supplied here

* `isCompactOperator_rieszProjection_horizontalInduction` — compactness of the
  Riesz projection `Q_{ε,n} = (2πi)⁻¹ ∮_{Γ_τ} (z − A_{ε,K})⁻¹ dz`, from the
  compact-resolvent clause of `lem:torus-sector-basic`: every state resolvent of
  `A_{ε,K}` is compact (`isCompactOperator_horizontalInduction_stateResolvent`).
* `finiteDimensional_rieszProjection_range_horizontalInduction` — "isolated
  eigenvalues of finite algebraic multiplicity" (proof of
  `prop:global-spectral-transfer`): a compact idempotent has finite-dimensional range.
* `exists_horizontalInduction_eigenpair_mem_ball_of_rieszProjection_ne_zero`
  and its `growthFloor` form — an eigenvalue in the region of the last sentence quoted above,
  located strictly inside `Γ_τ`, hence with
  `Γ_τ.growthFloor ≤ Re λ`.  Since `Γ_τ` is the seed contour shifted by `−iτ`,
  its growth floor is the seed's `g_*` — translation by `−iτ` does not change
  real parts.
* `ParametrixNeumannCorrection.ne_zero_of_inner_contour_test` — the trivial
  inner-product nonvanishing test used by `lem:global-riesz-nonzero`
  through `eq:global-projection-error`:
  `Re⟨Q f, f⟩ > 1/4` forces `Q ≠ 0`.
* The composite with the Section 8 finish bridge,
  `exists_growing_reducedInduction_eigenpair_of_horizontal_rieszProjection_ne_zero_full`:
  a nonvanishing horizontal Riesz projection produces a
  **three-component** reduced eigenpair at the contour's growth floor, for
  divergence-free `u` and `K ≠ 0`.  This is exactly the datum
  `MainReducedClauses` consumes.

## What is *not* claimed

Nothing here constructs a resolvent on `Γ_τ` or proves `Q ≠ 0`; those are
`lem:global-contour-resolvent` and `lem:global-riesz-nonzero`, the quantitative
content of Section 7, and they are proved in `Global/TorusParametrixError.lean` and
`Global/TorusGlobalRieszNonzero.lean`, assembled in `Global/TorusGlobalSpectralTransfer.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

/-! ## The inner-product nonvanishing test of `lem:global-riesz-nonzero` -/

namespace ParametrixNeumannCorrection

/--
An operator with a strictly positive real diagonal inner product at one vector
is nonzero.  This is the trivial half of `lem:global-riesz-nonzero`:
the quantitative work is the estimate
`eq:global-projection-error`, which produces the strict
inequality, after which nonvanishing of the projection is immediate.

The companion of `ne_zero_of_inner_contour_test`, which tests the same
inner product against an explicit threshold; both conclude `P ≠ 0` from one
nonzero vector.
-/
theorem ne_zero_of_inner_re_pos {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (P : X →L[ℂ] X) (f : X)
    (hf : 0 < (inner ℂ (P f) f : ℂ).re) : P ≠ 0 := by
  intro hP
  rw [hP] at hf
  simp at hf

/--
**The nonvanishing test of `lem:global-riesz-nonzero`** in the
exact numerical shape the paper uses: combining
`eq:global-projection-error` with the local spectral witness
`eq:local-spectral-witness` gives `Re⟨Q_{ε,n} f_n, f_n⟩ > 1/4`, and "in
particular `Q_{ε,n} ≠ 0`".
-/
theorem ne_zero_of_inner_contour_test {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (P : X →L[ℂ] X) (f : X)
    (hf : 1 / 4 < (inner ℂ (P f) f : ℂ).re) : P ≠ 0 :=
  ne_zero_of_inner_re_pos P f (by linarith)

end ParametrixNeumannCorrection

namespace HorizontalSpectralExtraction

open CorrectedRieszProjectionEigenmode

/-! ## Compactness and finite rank of the Riesz projection -/

/--
Every Riesz projection `Q_{ε,n} = (2πi)⁻¹ ∮_{Γ}(z − A_{ε,K})⁻¹ dz` of the
horizontal torus operator on a circle is compact.  This is the contour form of
the clause of `lem:torus-sector-basic` "its resolvent is compact", which the proof
of `prop:global-spectral-transfer` invokes.

Compactness of each state resolvent is free from the two-component Rellich
embedding, so the reference family in the compact-difference criterion can be
taken to be zero.
-/
theorem isCompactOperator_rieszProjection_horizontalInduction
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
    {center : ℂ} {radius : ℝ} (hradius : 0 ≤ radius)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      (sphere center radius)) :
    IsCompactOperator h.rieszProjection := by
  apply h.isCompactOperator_rieszProjection_of_compact_difference hradius
    (fun _z ↦ (0 : TransverseC2L2 →L[ℂ] TransverseC2L2)) continuousOn_const
  · intro z hz
    simpa using
      isCompactOperator_horizontalInduction_stateResolvent u epsilon K h z
  · unfold circleIntegral
    simp

/--
The Riesz range of any resolver of the horizontal torus operator on a
positive-radius circle is finite-dimensional.  This is the paper's "the
spectrum inside `Γ_τ` consists of isolated eigenvalues of finite algebraic
multiplicity" (proof of `prop:global-spectral-transfer`): the resolvent is compact, hence the Riesz
projection is a compact idempotent, and a compact projection has
finite-dimensional range.

No smallness, no contour closeness, and no inner product on the graph domain is
used.
-/
theorem finiteDimensional_rieszProjection_range_horizontalInduction
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
    {center : ℂ} {radius : ℝ} (hradius : 0 < radius)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      (sphere center radius)) :
    FiniteDimensional ℂ h.rieszProjection.toLinearMap.range :=
  h.finiteDimensional_rieszProjection_range_of_resolventSphere_and_isCompact
    hradius
    (isCompactOperator_rieszProjection_horizontalInduction u epsilon K
      hradius.le h)

/-- Spectral-circle form of
`finiteDimensional_rieszProjection_range_horizontalInduction`: a
`SpectralCircle` carries its own positive radius. -/
theorem finiteDimensional_rieszProjection_range_horizontalInduction_boundary
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) (Gamma : SpectralCircle)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      Gamma.boundary) :
    FiniteDimensional ℂ h.rieszProjection.toLinearMap.range :=
  finiteDimensional_rieszProjection_range_horizontalInduction u epsilon K
    Gamma.radius_pos h

/-! ## The extracted horizontal eigenpair -/

/--
**The eigenvalue extraction of `prop:global-spectral-transfer`** for the horizontal
two-component torus operator.

A nonzero Riesz projection `Q_{ε,n} ≠ 0` on a spectral circle `Γ` on whose
boundary the resolvent exists yields an eigenpair of `A_{ε,K}`, with an
`H²(T²; ℂ²)` eigenfunction, whose eigenvalue lies **strictly inside** `Γ`.
This is the paper's "the non-zero projection shows that this spectrum is
nonempty" (proof of `prop:global-spectral-transfer`), made explicit by choosing one
eigenvalue.

The two quantitative inputs of Section 7 are the hypotheses: `h` is
`lem:global-contour-resolvent` and `hne` is
`lem:global-riesz-nonzero`.
-/
theorem exists_horizontalInduction_eigenpair_mem_ball_of_rieszProjection_ne_zero
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) (Gamma : SpectralCircle)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      Gamma.boundary)
    (hne : h.rieszProjection ≠ 0) :
    ∃ (lam : ℂ) (hfun : TransverseC2H2),
      lam ∈ ball Gamma.center Gamma.radius ∧
        (horizontalInductionOperator u epsilon K).IsEigenpair lam hfun := by
  have hidempotent : IsIdempotentElem h.rieszProjection :=
    h.rieszProjection_isIdempotentElem_of_resolventSphere Gamma.radius_pos
  have hfinite : FiniteDimensional ℂ h.rieszProjection.toLinearMap.range :=
    finiteDimensional_rieszProjection_range_horizontalInduction_boundary
      u epsilon K Gamma h
  exact exists_domain_eigenpair_mem_ball_of_finite_projection h
    Gamma.radius_pos.le hidempotent hfinite hne

/-- Closed-region form of
`exists_horizontalInduction_eigenpair_mem_ball_of_rieszProjection_ne_zero`: the
extracted eigenvalue lies in the closed disc bounded by `Γ`, which is the
literal reading of "an eigenvalue inside `Γ_τ`" (statement of
`prop:global-spectral-transfer`). -/
theorem exists_horizontalInduction_eigenpair_mem_closedRegion_of_rieszProjection_ne_zero
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) (Gamma : SpectralCircle)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      Gamma.boundary)
    (hne : h.rieszProjection ≠ 0) :
    ∃ (lam : ℂ) (hfun : TransverseC2H2),
      lam ∈ Gamma.closedRegion ∧
        (horizontalInductionOperator u epsilon K).IsEigenpair lam hfun := by
  obtain ⟨lam, hfun, hball, heigen⟩ :=
    exists_horizontalInduction_eigenpair_mem_ball_of_rieszProjection_ne_zero
      u epsilon K Gamma h hne
  exact ⟨lam, hfun, ball_subset_closedBall hball, heigen⟩

/--
**The eigenvalue bound of `prop:global-spectral-transfer`** for the horizontal
torus operator: the extracted eigenvalue clears the contour's growth floor,
`λ^ε = α_ε + iω_ε` with `α_ε ≥ g_*`.

The rate is the contour's own `growthFloor = center.re − radius`, not
`lam.re`: it does not depend on the resolver, hence not on `epsilon`.  For the
selected contour `Γ_τ` — the seed contour shifted by `−iτ` — this number is the
seed's `g_*`, because "translation by `−iτ` preserves real parts"
(proof of `prop:global-spectral-transfer`).
-/
theorem exists_growthFloor_horizontalInduction_eigenpair_of_rieszProjection_ne_zero
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) (Gamma : SpectralCircle)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      Gamma.boundary)
    (hne : h.rieszProjection ≠ 0) :
    ∃ (lam : ℂ) (hfun : TransverseC2H2),
      Gamma.growthFloor ≤ lam.re ∧
        (horizontalInductionOperator u epsilon K).IsEigenpair lam hfun := by
  obtain ⟨lam, hfun, hball, heigen⟩ :=
    exists_horizontalInduction_eigenpair_mem_ball_of_rieszProjection_ne_zero
      u epsilon K Gamma h hne
  exact ⟨lam, hfun, SpectralCircle.growthFloor_le_re_of_mem_ball hball, heigen⟩

/-! ## The composite with the Section 8 axial recovery -/

/--
The same composite, keeping every conclusion of the axial recovery: the
recovered mode is divergence-free in its sector
(`fixedSectorDivergence K b = 0`) and its axial lift
`V^ε = e^{2πiKx₃} b` is a divergence-free `H²(T³; ℂ³)` eigenmode of the
auxiliary product operator `L_{ε,u}` (proof of `thm:main`).

The `Div V = 0` clauses come from the paper's own Section 8 construction
(`lem:axial-recovery`, Lemma 8.1), not from the auxiliary solenoidality
theorem of `FastDynamo/Finish/RealSolution.lean`.
-/
theorem exists_growing_reducedInduction_eigenpair_of_horizontal_rieszProjection_ne_zero_full
    (u : TransverseRealW1Inf) (hdiv : IsTransverseDivergenceFree u)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {K : ℤ} (hK : K ≠ 0)
    (Gamma : SpectralCircle)
    (h : HasResolventOn (horizontalInductionOperator u epsilon K)
      Gamma.boundary)
    (hne : h.rieszProjection ≠ 0) :
    ∃ (lam : ℂ) (b : TransverseC3H2),
      Gamma.growthFloor ≤ lam.re ∧
        (reducedInductionOperator u epsilon K).IsEigenpair lam b ∧
        (productInductionOperator u epsilon).IsEigenpair lam (axialLiftH2 K b) ∧
        fixedSectorDivergence K b = 0 ∧
        productDivergenceFromH2 (axialLiftH2 K b) = 0 := by
  obtain ⟨lam, hfun, hfloor, hpair⟩ :=
    exists_growthFloor_horizontalInduction_eigenpair_of_rieszProjection_ne_zero
      u epsilon K Gamma h hne
  obtain ⟨b, hb, -, -, hsector, hlift⟩ :=
    exists_reducedInductionEigenpair_of_horizontalEigenpair u hdiv hepsilon hK
      hpair
  exact ⟨lam, b, hfloor, hb,
    (productInductionEigenpair_axialLiftH2_iff_reduced u epsilon K lam b).2 hb,
    hsector, hlift⟩

end HorizontalSpectralExtraction

end

end FastDynamo
