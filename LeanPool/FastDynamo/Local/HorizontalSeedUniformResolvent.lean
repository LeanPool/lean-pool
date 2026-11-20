/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalSeedResolventH2
public import LeanPool.FastDynamo.Local.HorizontalRieszPerturbation

/-!
# Uniform-in-`δ` packaging of the seed resolvent

`prop:local-seed` asks for **one** constant `L`
with `‖R_δ(ζ)‖_{L²→H¹} ≤ L` for every `ζ ∈ Γ` and every `δ ∈ I = [δ₋, δ₊]`; this module
produces the stronger `L² → H²` constant, which the domain-valued `HasResolventOn` of the Lean
development carries anyway and which the paper's bound follows from.  The two
ingredients it starts from are each `δ`-dependent:

* the seed bound of `HorizontalMode.exists_horizontalSeedWitness` is defined through
  `Classical.choose` of a compactness argument, so it carries no information about how it
  varies with `δ`;
* `HorizontalMode.exists_seedNeumannData` does give a `δ`-uniform bound, but for
  the `L² → H¹` solution map `horizontalDeltaSolution`, not for the graph-valued resolvent.

This module supplies the uniform bound.  It bounds the graph-valued form resolvent by the norm
of the solution map (`norm_formPencilDomainInverse_le`), bounds the pair map of the `H²` lift
uniformly for `δ` in a compact positive interval (`norm_horizontalStrongPairMap_le_bound`),
and assembles the two into `horizontalLocalResolventBoundOfBounds`, a
`WholePlaneLocalResolventBound` whose constant is supplied by the caller.

It also records that the strong resolvent of `prop:local-seed` and the form resolvent it is
built from have the *same* ambient state resolvent, hence the **same Riesz projection**
(`horizontalStrongResolvent_rieszProjection`).  That is what transports
`eq:local-spectral-witness` from the form operator `A_{v_h,δ}`, where it is proved, to
the strong operator `𝓛_δ = horizontalLocalOperator N δ v`, which is the operator
`Reduction/ExactScalingC2.lean` and §7 consume.

## Main results

* `norm_formPencilGraphPair_le`, `norm_formPencilDomainInverse_le`,
  `norm_formPencilHasResolventOn_inv_le` — the graph-norm bound `‖R‖ + (1 + ‖z‖‖j‖‖R‖)`.
* `HorizontalWeakForm.HorizontalNeumannData.norm_contourResolvent_inv_le` — the same for the
  Neumann data of the seed contour.
* `HorizontalWeakForm.norm_horizontalStrongPairMap_le_bound` — the `δ`-uniform pair bound.
* `HorizontalWeakForm.horizontalLocalResolventBoundOfBounds` — the packaged seed bound.
* `HorizontalWeakForm.horizontalStrongResolvent_rieszProjection` — equality of the Riesz
  projections of the strong and of the form operator.
-/

@[expose] public section


namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## Generic: the graph norm of the pencil solution map -/

section FormPencilNorm

universe u v

variable {V : Type u} {X : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]

omit [CompleteSpace V] in
/-- The graph pair `f ↦ (R f, f - z j (R f))` has norm at most `‖R‖ + 1 + ‖z‖‖j‖‖R‖`. -/
theorem norm_formPencilGraphPair_le (j : V →L[ℂ] X) (z : ℂ) (R : X →L[ℂ] V) :
    ‖formPencilGraphPair j z R‖ ≤ ‖R‖ + (1 + ‖z‖ * (‖j‖ * ‖R‖)) := by
  have hR0 : (0 : ℝ) ≤ ‖R‖ := ContinuousLinearMap.opNorm_nonneg R
  have hj0 : (0 : ℝ) ≤ ‖j‖ := ContinuousLinearMap.opNorm_nonneg j
  have hz0 : (0 : ℝ) ≤ ‖z‖ * (‖j‖ * ‖R‖) :=
    mul_nonneg (norm_nonneg z) (mul_nonneg hj0 hR0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun f => ?_
  have hf0 : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  rw [formPencilGraphPair_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · refine (R.le_opNorm f).trans ?_
    have : ‖R‖ * ‖f‖ ≤ (‖R‖ + (1 + ‖z‖ * (‖j‖ * ‖R‖))) * ‖f‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hf0
    exact this
  · have hstep : ‖f - z • j (R f)‖ ≤ ‖f‖ + ‖z‖ * (‖j‖ * (‖R‖ * ‖f‖)) := by
      refine (norm_sub_le f (z • j (R f))).trans ?_
      have h1 : ‖z • j (R f)‖ = ‖z‖ * ‖j (R f)‖ := by rw [norm_smul]
      have h2 : ‖j (R f)‖ ≤ ‖j‖ * (‖R‖ * ‖f‖) :=
        (j.le_opNorm (R f)).trans (mul_le_mul_of_nonneg_left (R.le_opNorm f) hj0)
      have h3 : ‖z • j (R f)‖ ≤ ‖z‖ * (‖j‖ * (‖R‖ * ‖f‖)) := by
        rw [h1]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg z)
      linarith
    have hexp : (‖R‖ + (1 + ‖z‖ * (‖j‖ * ‖R‖))) * ‖f‖ =
        ‖R‖ * ‖f‖ + (‖f‖ + ‖z‖ * (‖j‖ * (‖R‖ * ‖f‖))) := by ring
    have hprod : (0 : ℝ) ≤ ‖R‖ * ‖f‖ := mul_nonneg hR0 hf0
    linarith [hstep, hexp, hprod]

omit [CompleteSpace V] in
/-- The graph-valued solution map inherits the bound of `norm_formPencilGraphPair_le`. -/
theorem norm_formPencilDomainInverse_le (j : V →L[ℂ] X) (a : ComplexForm V) (z : ℂ)
    (R : X →L[ℂ] V)
    (hR : ∀ (f : X) (phi : V),
      a (R f) phi + z * inner ℂ (j phi) (j (R f)) = inner ℂ (j phi) f) :
    ‖formPencilDomainInverse j a z R hR‖ ≤ ‖R‖ + (1 + ‖z‖ * (‖j‖ * ‖R‖)) := by
  have h : (AssociatedFormProdDomain j a).subtypeL.comp
      (formPencilDomainInverse j a z R hR) = formPencilGraphPair j z R :=
    subtypeL_comp_codRestrict (AssociatedFormProdDomain j a) (formPencilGraphPair j z R)
      (formPencilGraphPair_mem j a z R hR)
  calc ‖formPencilDomainInverse j a z R hR‖
      = ‖(AssociatedFormProdDomain j a).subtypeL.comp
          (formPencilDomainInverse j a z R hR)‖ :=
        (norm_subtypeL_comp (AssociatedFormProdDomain j a)
          (formPencilDomainInverse j a z R hR)).symm
    _ = ‖formPencilGraphPair j z R‖ := congrArg (fun T : X →L[ℂ] V × X => ‖T‖) h
    _ ≤ ‖R‖ + (1 + ‖z‖ * (‖j‖ * ‖R‖)) := norm_formPencilGraphPair_le j z R

omit [CompleteSpace V] in
/-- The chosen graph-valued resolvent of `formPencilHasResolventOn` is bounded by the norm of
the solution map. -/
theorem norm_formPencilHasResolventOn_inv_le (j : V →L[ℂ] X) (hj : Function.Injective j)
    (hdense : DenseRange j) (a : ComplexForm V) {S : Set ℂ} (R : ℂ → X →L[ℂ] V)
    (hR : ∀ z ∈ S, ∀ (f : X) (phi : V),
      a (R z f) phi + z * inner ℂ (j phi) (j (R z f)) = inner ℂ (j phi) f)
    (hinj : ∀ z ∈ S, ∀ e : V, (∀ phi : V, a e phi + z * inner ℂ (j phi) (j e) = 0) → e = 0)
    (hcont : ContinuousOn R S) {z : ℂ} (hz : z ∈ S) :
    ‖(formPencilHasResolventOn j hj hdense a R hR hinj hcont).inv z‖ ≤
      ‖R z‖ + (1 + ‖z‖ * (‖j‖ * ‖R z‖)) := by
  rw [formPencilHasResolventOn_inv j hj hdense a R hR hinj hcont hz]
  exact norm_formPencilDomainInverse_le j a z (R z) (hR z hz)

end FormPencilNorm

/-! ## The bound on a spectral circle -/

/-- Every point of a circle is at distance at most `‖c‖ + R` from the origin. -/
theorem norm_le_of_mem_sphere {c : ℂ} {R : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere c R) :
    ‖z‖ ≤ ‖c‖ + R := by
  have hd : ‖z - c‖ = R := by
    simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hz)
  calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
    _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le c (z - c)
    _ = ‖c‖ + R := by rw [hd]

/-! ## Generic: equality of Riesz projections -/

namespace HasResolventOn

universe u' v' w'

variable {X : Type u'} {D : Type v'} {D' : Type w'}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup D'] [NormedSpace ℂ D']

omit [CompleteSpace X] in
/-- Two resolvents on the same circle with the same ambient state resolvent — possibly of two
different operators, with two different bundled domains — have the same Riesz projection. -/
theorem rieszProjection_congr_of_domains {A : DomainOperator X D} {B : DomainOperator X D'}
    {c : ℂ} {R : ℝ} (hA : HasResolventOn A (Metric.sphere c R))
    (hB : HasResolventOn B (Metric.sphere c R))
    (h : ∀ z : ℂ, hA.stateResolvent z = hB.stateResolvent z) :
    hA.rieszProjection = hB.rieszProjection := by
  have hfun : hA.stateResolvent = hB.stateResolvent := funext h
  unfold HasResolventOn.rieszProjection
  rw [hfun]

end HasResolventOn

namespace HorizontalWeakForm

/-! ## The graph-norm bound for the perturbed seed resolvent -/

/-- The graph-valued resolvent of `𝓛_{w',δ}` built from the Neumann series is bounded by the
norm of the perturbed solution map. -/
theorem norm_horizontalDeltaHasResolventOn_inv_le (N delta : ℝ) (w' w : WholePlaneC3LInf)
    (S : Set ℂ) (hSre : ∀ z ∈ S, 0 < z.re)
    (hSinv : ∀ z ∈ S, (horizontalPencilForm N w z).IsInvertible)
    (hSlt : ∀ z ∈ S, horizontalNeumannSize N delta w' w z < 1) {z : ℂ} (hz : z ∈ S) :
    ‖(horizontalDeltaHasResolventOn N delta w' w S hSre hSinv hSlt).inv z‖ ≤
      ‖horizontalDeltaSolution N delta w' w z‖ +
        (1 + ‖z‖ * (‖wholePlaneH1Embedding C2‖ *
          ‖horizontalDeltaSolution N delta w' w z‖)) :=
  norm_formPencilHasResolventOn_inv_le _ _ _ _ _ _ _ _ hz

namespace HorizontalNeumannData

variable {N delta : ℝ} {w' w : WholePlaneC3LInf} {lam : ℂ}
  {iso : HorizontalIsolation N w lam}

/-- **The graph-norm bound on the contour.**  On `Γ` the graph-valued resolvent of the
perturbed generator is controlled by the `L² → H¹` norm of the perturbed solution map, which
`HorizontalMode.exists_seedNeumannData` bounds uniformly in `h` and `δ`. -/
theorem norm_contourResolvent_inv_le (nd : HorizontalNeumannData N delta w' w lam iso)
    {z : ℂ} (hz : z ∈ Metric.sphere lam iso.radius) :
    ‖nd.contourResolvent.inv z‖ ≤
      ‖horizontalDeltaSolution N delta w' w z‖ +
        (1 + ‖z‖ * (‖wholePlaneH1Embedding C2‖ *
          ‖horizontalDeltaSolution N delta w' w z‖)) :=
  norm_horizontalDeltaHasResolventOn_inv_le N delta w' w iso.neumannOpen
    (fun y hy => iso.neumannSet_re_pos y (iso.neumannOpen_subset_neumannSet hy))
    (fun y hy => iso.neumannSet_isInvertible y (iso.neumannOpen_subset_neumannSet hy))
    (fun _y hy => nd.size_lt_one (iso.neumannOpen_subset_neumannSet hy))
    (iso.sphere_subset_neumannOpen hz)

end HorizontalNeumannData

/-! ## The `δ`-uniform bound for the pair map of the `H²` lift -/

/-- The velocity part of the Laplacian datum, i.e. everything in
`horizontalLaplacianDatum` except the `δ N²` mass term. -/
def horizontalVelocityDatumBound (N : ℝ) (v : WholePlaneVelocityCoefficients) : ℝ :=
  ‖horizontalTransport v.value‖ + ‖horizontalAxialTransport N v.value‖ +
    ‖horizontalStretching v‖

/-- The Laplacian datum of `𝔩_{w,δ}` is bounded by `|δ| N² ‖j‖` plus a `δ`-free constant. -/
theorem norm_horizontalLaplacianDatum_le (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) :
    ‖horizontalLaplacianDatum N delta v‖ ≤
      |delta| * N ^ 2 * ‖wholePlaneH1Embedding C2‖ + horizontalVelocityDatumBound N v := by
  have hmass : ‖((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2‖ =
      |delta| * N ^ 2 * ‖wholePlaneH1Embedding C2‖ := by
    rw [norm_smul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]
  have hstep : ‖horizontalLaplacianDatum N delta v‖ ≤
      ‖((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2 +
          horizontalTransport v.value + horizontalAxialTransport N v.value‖ +
        ‖horizontalStretching v‖ :=
    norm_sub_le _ _
  have h2 : ‖((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2 +
      horizontalTransport v.value + horizontalAxialTransport N v.value‖ ≤
      ‖((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2 +
        horizontalTransport v.value‖ + ‖horizontalAxialTransport N v.value‖ :=
    norm_add_le _ _
  have h3 : ‖((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2 +
      horizontalTransport v.value‖ ≤
      ‖((delta : ℂ) * (N : ℂ) ^ 2) • wholePlaneH1Embedding C2‖ +
        ‖horizontalTransport v.value‖ :=
    norm_add_le _ _
  simp only [horizontalVelocityDatumBound]
  linarith [hstep, h2, h3, hmass.le, hmass.ge]

/-- The uniform bound for the pair map of the `H²` lift, for `δ` in `[δ₋, δ₊]` with
`δ₋ > 0`. -/
def horizontalStrongPairBound (N deltaLower deltaUpper : ℝ)
    (v : WholePlaneVelocityCoefficients) : ℝ :=
  max ‖wholePlaneH1Embedding C2‖
    (deltaLower⁻¹ * (1 + (deltaUpper * N ^ 2 * ‖wholePlaneH1Embedding C2‖ +
      horizontalVelocityDatumBound N v)))

/-- The uniform pair bound is nonnegative. -/
theorem horizontalStrongPairBound_nonneg (N deltaLower deltaUpper : ℝ)
    (v : WholePlaneVelocityCoefficients) :
    0 ≤ horizontalStrongPairBound N deltaLower deltaUpper v :=
  le_trans (ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2))
    (le_max_left _ _)

/-- The first component of the pair map is the `L²` value of the graph element. -/
theorem norm_horizontalStrongPairMap_fst_le (a : ComplexForm WholePlaneC2H1)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    ‖wholePlaneH1Embedding C2 u.1.1‖ ≤ ‖wholePlaneH1Embedding C2‖ * ‖u‖ :=
  le_trans ((wholePlaneH1Embedding C2).le_opNorm u.1.1)
    (mul_le_mul_of_nonneg_left (norm_fst_le u.1)
      (ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2)))

/-- The image of a graph element under the associated operator is bounded by its graph
norm. -/
theorem norm_horizontalAssociatedOperator_op_le (a : ComplexForm WholePlaneC2H1)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    ‖(horizontalAssociatedOperator a).op u‖ ≤ ‖u‖ := by
  have hop : (horizontalAssociatedOperator a).op u = -u.1.2 := rfl
  calc ‖(horizontalAssociatedOperator a).op u‖
      = ‖-u.1.2‖ := congrArg (fun t : WholePlaneC2L2 => ‖t‖) hop
    _ = ‖u.1.2‖ := norm_neg _
    _ ≤ ‖u‖ := norm_snd_le u.1

/-- The second component of the pair map, the `L²` representative of `Δ_⊥ b`. -/
theorem norm_horizontalStrongPairMap_snd_le (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (a : ComplexForm WholePlaneC2H1)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    ‖((delta : ℂ)⁻¹) • ((horizontalAssociatedOperator a).op u +
        horizontalLaplacianDatum N delta v u.1.1)‖ ≤
      (|delta|⁻¹ * (1 + ‖horizontalLaplacianDatum N delta v‖)) * ‖u‖ := by
  have hinv0 : (0 : ℝ) ≤ |delta|⁻¹ := inv_nonneg.mpr (abs_nonneg delta)
  have hdatum : ‖horizontalLaplacianDatum N delta v u.1.1‖ ≤
      ‖horizontalLaplacianDatum N delta v‖ * ‖u‖ :=
    le_trans ((horizontalLaplacianDatum N delta v).le_opNorm u.1.1)
      (mul_le_mul_of_nonneg_left (norm_fst_le u.1)
        (ContinuousLinearMap.opNorm_nonneg (horizontalLaplacianDatum N delta v)))
  have hsum : ‖(horizontalAssociatedOperator a).op u +
      horizontalLaplacianDatum N delta v u.1.1‖ ≤
      (1 + ‖horizontalLaplacianDatum N delta v‖) * ‖u‖ := by
    have hadd := norm_add_le ((horizontalAssociatedOperator a).op u)
      (horizontalLaplacianDatum N delta v u.1.1)
    have hopn := norm_horizontalAssociatedOperator_op_le a u
    have hring : (1 + ‖horizontalLaplacianDatum N delta v‖) * ‖u‖ =
        ‖u‖ + ‖horizontalLaplacianDatum N delta v‖ * ‖u‖ := by ring
    linarith
  have hc : ‖((delta : ℂ)⁻¹)‖ = |delta|⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc ‖((delta : ℂ)⁻¹) • ((horizontalAssociatedOperator a).op u +
        horizontalLaplacianDatum N delta v u.1.1)‖
      = |delta|⁻¹ * ‖(horizontalAssociatedOperator a).op u +
          horizontalLaplacianDatum N delta v u.1.1‖ :=
        (norm_smul ((delta : ℂ)⁻¹) ((horizontalAssociatedOperator a).op u +
            horizontalLaplacianDatum N delta v u.1.1)).trans
          (congrArg (fun t : ℝ => t * ‖(horizontalAssociatedOperator a).op u +
            horizontalLaplacianDatum N delta v u.1.1‖) hc)
    _ ≤ |delta|⁻¹ * ((1 + ‖horizontalLaplacianDatum N delta v‖) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hsum hinv0
    _ = (|delta|⁻¹ * (1 + ‖horizontalLaplacianDatum N delta v‖)) * ‖u‖ := by ring

/-- The pair map `(j b, δ⁻¹(A b + 𝔡 b))` of the `H²` lift is bounded by any `P` dominating
both `‖j‖` and `|δ|⁻¹(1 + ‖𝔡‖)`. -/
theorem norm_horizontalStrongPairMap_le (N delta : ℝ) (v : WholePlaneVelocityCoefficients)
    (a : ComplexForm WholePlaneC2H1) {P : ℝ}
    (h1 : ‖wholePlaneH1Embedding C2‖ ≤ P)
    (h2 : |delta|⁻¹ * (1 + ‖horizontalLaplacianDatum N delta v‖) ≤ P) :
    ‖horizontalStrongPairMap N delta v a‖ ≤ P := by
  have hP0 : (0 : ℝ) ≤ P :=
    le_trans (ContinuousLinearMap.opNorm_nonneg (wholePlaneH1Embedding C2)) h1
  refine ContinuousLinearMap.opNorm_le_bound _ hP0 fun u => ?_
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hval : ‖horizontalStrongPairMap N delta v a u‖ =
      max ‖wholePlaneH1Embedding C2 u.1.1‖
        ‖((delta : ℂ)⁻¹) • ((horizontalAssociatedOperator a).op u +
          horizontalLaplacianDatum N delta v u.1.1)‖ := Prod.norm_def _
  rw [hval]
  refine max_le ?_ ?_
  · exact (norm_horizontalStrongPairMap_fst_le a u).trans
      (mul_le_mul_of_nonneg_right h1 hu0)
  · exact (norm_horizontalStrongPairMap_snd_le N delta v a u).trans
      (mul_le_mul_of_nonneg_right h2 hu0)

/-- **The `δ`-uniform pair bound.**  For `δ ∈ [δ₋, δ₊]` with `δ₋ > 0` the pair map of the
`H²` lift is bounded by the `δ`-free constant `horizontalStrongPairBound`. -/
theorem norm_horizontalStrongPairMap_le_bound (N : ℝ) (v : WholePlaneVelocityCoefficients)
    (a : ComplexForm WholePlaneC2H1) {deltaLower deltaUpper delta : ℝ}
    (hdl : 0 < deltaLower) (hlow : deltaLower ≤ delta) (hupp : delta ≤ deltaUpper) :
    ‖horizontalStrongPairMap N delta v a‖ ≤
      horizontalStrongPairBound N deltaLower deltaUpper v := by
  have hdelta0 : 0 < delta := lt_of_lt_of_le hdl hlow
  have habs : |delta| = delta := abs_of_pos hdelta0
  have hinv : |delta|⁻¹ ≤ deltaLower⁻¹ := by
    rw [habs, inv_le_inv₀ hdelta0 hdl]
    exact hlow
  have hdat : ‖horizontalLaplacianDatum N delta v‖ ≤
      deltaUpper * N ^ 2 * ‖wholePlaneH1Embedding C2‖ + horizontalVelocityDatumBound N v := by
    refine (norm_horizontalLaplacianDatum_le N delta v).trans ?_
    have hj0 : (0 : ℝ) ≤ ‖wholePlaneH1Embedding C2‖ :=
      ContinuousLinearMap.opNorm_nonneg _
    have hN0 : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
    have : |delta| * N ^ 2 * ‖wholePlaneH1Embedding C2‖ ≤
        deltaUpper * N ^ 2 * ‖wholePlaneH1Embedding C2‖ := by
      rw [habs]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hupp hN0) hj0
    linarith
  refine norm_horizontalStrongPairMap_le N delta v a (le_max_left _ _) ?_
  refine le_trans ?_ (le_max_right ‖wholePlaneH1Embedding C2‖ _)
  have hpos : (0 : ℝ) ≤ 1 + ‖horizontalLaplacianDatum N delta v‖ := by
    have := ContinuousLinearMap.opNorm_nonneg (horizontalLaplacianDatum N delta v)
    linarith
  have hinvpos : (0 : ℝ) ≤ deltaLower⁻¹ := (inv_pos.mpr hdl).le
  calc |delta|⁻¹ * (1 + ‖horizontalLaplacianDatum N delta v‖)
      ≤ deltaLower⁻¹ * (1 + ‖horizontalLaplacianDatum N delta v‖) :=
        mul_le_mul_of_nonneg_right hinv hpos
    _ ≤ deltaLower⁻¹ * (1 + (deltaUpper * N ^ 2 * ‖wholePlaneH1Embedding C2‖ +
          horizontalVelocityDatumBound N v)) := by
        refine mul_le_mul_of_nonneg_left ?_ hinvpos
        linarith

/-! ## The strong resolvent and the form resolvent have the same Riesz projection -/

/-- The strong resolvent of `prop:local-seed` has the same ambient state resolvent as the
form resolvent it is built from: both send `f` to the `L²` value of the solution of the weak
equation. -/
theorem horizontalStrongResolvent_stateResolvent (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (a : ComplexForm WholePlaneC2H1)
    (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    {S : Set ℂ} (hres : HasResolventOn (horizontalAssociatedOperator a) S) (z : ℂ) :
    (horizontalStrongResolvent N delta v a hdelta hv hform hres).stateResolvent z =
      hres.stateResolvent z := by
  refine ContinuousLinearMap.ext fun f => ?_
  exact wholePlaneH2Embedding_horizontalStrongLift N delta v a hdelta hv hform (hres.inv z f)

/-- **The Riesz projection of `𝓛_δ` is the Riesz projection of the form operator `A_{w,δ}`.**
This is what transports `eq:local-spectral-witness`, proved for the form operator in
`Local/HorizontalRieszPerturbation.lean`, to the strong operator consumed by
`Reduction/ExactScalingC2.lean`. -/
theorem horizontalStrongResolvent_rieszProjection (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (a : ComplexForm WholePlaneC2H1)
    (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    {c : ℂ} {R : ℝ}
    (hres : HasResolventOn (horizontalAssociatedOperator a) (Metric.sphere c R)) :
    (horizontalStrongResolvent N delta v a hdelta hv hform hres).rieszProjection =
      hres.rieszProjection :=
  HasResolventOn.rieszProjection_congr_of_domains _ _
    (horizontalStrongResolvent_stateResolvent N delta v a hdelta hv hform hres)

/-! ## The packaged uniform seed bound -/

/-- The `L² → H²` resolvent family is bounded by the product of the pair-map bound and the
graph-norm bound of the form resolvent. -/
theorem norm_horizontalStrongInv_le_of_bounds (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (a : ComplexForm WholePlaneC2H1)
    (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    {S : Set ℂ} (hres : HasResolventOn (horizontalAssociatedOperator a) S) {P C : ℝ}
    (hP : ‖horizontalStrongPairMap N delta v a‖ ≤ P) (hP0 : 0 ≤ P) {z : ℂ}
    (hC : ‖hres.inv z‖ ≤ C) :
    ‖horizontalStrongInv N delta v a hdelta hv hform hres z‖ ≤
      ‖wholePlaneH2OfPair C2‖ * (P * C) := by
  have hstep : ‖horizontalStrongInv N delta v a hdelta hv hform hres z‖ ≤
      ‖wholePlaneH2OfPair C2‖ *
        ‖horizontalStrongPairCod N delta v a hdelta hv hform hres z‖ :=
    ContinuousLinearMap.opNorm_comp_le (wholePlaneH2OfPair C2)
      (horizontalStrongPairCod N delta v a hdelta hv hform hres z)
  refine hstep.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (wholePlaneH2OfPair C2))
  rw [norm_horizontalStrongPairCod]
  refine (ContinuousLinearMap.opNorm_comp_le (horizontalStrongPairMap N delta v a)
    (hres.inv z)).trans ?_
  exact mul_le_mul hP hC (ContinuousLinearMap.opNorm_nonneg (hres.inv z)) hP0

/--
**`eq:local-continuation-bound` with a caller-supplied constant.**  Unlike the seed bound of
`HorizontalMode.exists_horizontalSeedWitness`, whose constant is chosen by `Classical.choose`
and therefore carries no
information about its dependence on `δ`, this one takes the two bounds as hypotheses, so a
`δ`-uniform constant can be supplied.
-/
def horizontalLocalResolventBoundOfBounds (N delta : ℝ)
    (v : WholePlaneVelocityCoefficients) (a : ComplexForm WholePlaneC2H1)
    (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    {S : Set ℂ} (hres : HasResolventOn (horizontalAssociatedOperator a) S) {P C L : ℝ}
    (hP : ‖horizontalStrongPairMap N delta v a‖ ≤ P) (hP0 : 0 ≤ P)
    (hC : ∀ z ∈ S, ‖hres.inv z‖ ≤ C)
    (hL : ‖wholePlaneH2OfPair C2‖ * (P * C) ≤ L) :
    WholePlaneLocalResolventBound v N delta S L where
  resolvent := horizontalStrongResolvent N delta v a hdelta hv hform hres
  norm_inv_le := fun z hz =>
    le_trans (norm_horizontalStrongInv_le_of_bounds N delta v a hdelta hv hform hres hP hP0
      (hC z hz)) hL

end HorizontalWeakForm

end

end FastDynamo
