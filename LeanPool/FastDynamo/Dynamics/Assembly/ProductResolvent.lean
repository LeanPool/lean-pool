/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Assembly.AxialSectorDomain
public import LeanPool.FastDynamo.Dynamics.Assembly.UniformSectorResolvent
public import LeanPool.FastDynamo.Dynamics.ReducedInductionHilleYosidaRay

/-!
# Assembling the sector resolvents into the all-frequency resolvent

`FastDynamo/Dynamics/ReducedInductionHilleYosidaRay.lean` provides, for every axial frequency `K`, a
Hille–Yosida ray `reducedInductionHilleYosidaRay u hu ε hε K` of the reduced operator
`A_{ε,K} = reducedInductionOperator u ε K` with the `K`-independent constant
`M_u = ‖transverseStretchingCoefficient u‖`, and in particular a two-sided domain-valued
resolvent on the whole coercive half-plane `{Re z > M_u}`.  This module sums those sector
resolvents into a resolvent of the all-frequency operator
`A = productInductionOperator u ε : DomainOperator ProductC3L2 ProductC3H2`, and packages the
result as `productHilleYosidaRay`, the single input the abstract generation theorem needs.

## Contents

* **The pencil is block diagonal.**  `productInductionPencil_axialLiftH2_eq_axialLiftL2`
  restates `productInductionPencil_axialLiftH2` in terms of the reduced pencil,
  `(z - A)(axialLiftH2 K b) = axialLiftL2 K ((z - A_{ε,K}) b)`; dually,
  `axialSectorProjL2_productInductionPencil` reads off the `K`-th sector of `(z - A) B`.
* **Summing a family of sector lifts.**  `exists_hasSum_axialLiftH2_of_summable_norm_sq` is the
  analytic engine: an arbitrary family `b : ℤ → TransverseC3H2` whose lifts are
  square-summable in the graph norm sums, in `ProductC3H2`, to an element whose squared graph
  norm is at most the sum of the squared graph norms.  The physical halves form an orthogonal
  family (`orthogonalFamily_axialLiftL2`) and are summed through `axialDecomposition`; the
  stored certificates are `lp.single`-supported at the axial frequency of their sector and are
  summed through `lp.hasSum_single`; the two limits are glued by closedness of
  `productH2Submodule`.  The statement is general: nothing beyond square
  summability is assumed of `b`.
* **The assembled inverse.**  `productResolventInv u hu hε z` is `x ↦ ∑' K, axialLiftH2 K
  (R_K(z) (P_K x))` on the half-plane and `0` elsewhere.  Square summability of the summands
  comes from the uniform graph bound `norm_axialLiftH2_le_graph` of
  `FastDynamo/Dynamics/Assembly/UniformSectorResolvent.lean` together with the sector bound
  `‖R_K(z)‖ ≤ (Re z - M_u)⁻¹`, which converts `∑_K ‖P_K x‖² = ‖x‖²` into a bound for the sum;
  this is the one place where the `K`-uniform elliptic estimate is used.
  `axialSectorProjH2_productResolventInv` recovers the sector data from the sum.
* **The two inverse equations and the packaging.**  Both hold sector by sector and are
  transported through `HasSum.unique`.  Continuity of `z ↦ productResolventInv z` is not proved
  by hand: the pointwise inverses are first fed to the repository's rational propagation
  construction `DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses`
  (`productResolventPropagated`), whose stored inverse is continuous and, by uniqueness of
  two-sided pencil inverses, agrees with the sector sum on the half-plane
  (`productResolventPropagated_inv`); `continuousOn_productResolventInv` transports it back.
  `productInductionHalfPlaneResolvent` then stores `productResolventInv` itself,
  the Parseval bound `norm_stateResolvent_productInduction_le` is immediate, and
  `HilleYosidaRay.ofHalfPlane` finishes.

The Hille–Yosida constant is not recomputed at the product level: it is the sector constant
`M_u`, which is independent of `ε` and of the axial frequency, and the Parseval identity
`hasSum_norm_sq_axialSector` turns the sector estimates into the same estimate for the sum.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped ENNReal

/-! ## Block diagonality of the all-frequency pencil -/

/--
**The all-frequency pencil restricted to one axial sector.**  On the lift of a transverse
amplitude, `z - A` is the axial lift of the reduced pencil `z - A_{ε,K}`.  This is
`productInductionPencil_axialLiftH2` followed by `fixedSectorInductionPencil_intertwines`.
-/
theorem productInductionPencil_axialLiftH2_eq_axialLiftL2
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ) (b : TransverseC3H2) :
    (productInductionOperator u ε).pencil z (axialLiftH2 K b) =
      axialLiftL2 K ((reducedInductionOperator u ε K).pencil z b) := by
  rw [productInductionPencil_axialLiftH2, fixedSectorInductionPencil_intertwines]

/--
**The `K`-th sector of the all-frequency pencil.**  Dually to
`productInductionPencil_axialLiftH2_eq_axialLiftL2`, the sector projection of `(z - A) B` is
the reduced pencil applied to the sector projection of `B`; this is block diagonality of the
induction action (`axialSectorProjL2_productInductionAction`) plus compatibility of the two
sector projections with the embeddings.
-/
theorem axialSectorProjL2_productInductionPencil (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ)
    (z : ℂ) (B : ProductC3H2) :
    axialSectorProjL2 K ((productInductionOperator u ε).pencil z B)
      = (reducedInductionOperator u ε K).pencil z (axialSectorProjH2 K B) := by
  change axialSectorProjL2 K (z • productH2Embedding B - productInductionAction u ε B)
    = z • transverseH2Embedding (axialSectorProjH2 K B) -
      reducedInductionAction u ε K (axialSectorProjH2 K B)
  rw [map_sub, map_smul, axialSectorProjL2_productInductionAction,
    transverseH2Embedding_axialSectorProjH2]

/-! ## Square-summable families of axial sectors -/

/-- Parseval for an `ℓ²` space of Banach spaces, with the exponent read as a natural power. -/
private theorem hasSum_norm_sq_lp_two {α : Type*} {E : α → Type*}
    [(i : α) → NormedAddCommGroup (E i)] (f : lp E 2) :
    HasSum (fun i => ‖(f : ∀ i, E i) i‖ ^ 2) (‖f‖ ^ 2) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := lp.hasSum_norm hp f
  rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num] at h
  simpa only [Real.rpow_natCast] using h

/-- Membership in `ℓ²` from summability of the squared norms, with the exponent read as a
natural power. -/
private theorem memℓp_two_of_summable_norm_sq {α : Type*} {E : α → Type*}
    [(i : α) → NormedAddCommGroup (E i)] (f : ∀ i, E i)
    (hf : Summable fun i => ‖f i‖ ^ 2) : Memℓp f 2 := by
  refine memℓp_gen ?_
  rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num]
  simpa only [Real.rpow_natCast] using hf

/--
**Summing axial modes in `L²`.**  A square-summable family of transverse amplitudes lifts to a
summable family of axial modes, and Parseval computes the norm of the sum.  This is
`IsHilbertSum.hasSum_linearIsometryEquiv_symm` for the axial decomposition of
`FastDynamo/Dynamics/Assembly/AxialHilbertSum.lean`.
-/
theorem exists_hasSum_axialLiftL2 (c : ℤ → TransverseC3L2)
    (hc : Summable fun K : ℤ => ‖c K‖ ^ 2) :
    ∃ V : ProductC3L2, HasSum (fun K : ℤ => axialLiftL2 K (c K)) V ∧
      ‖V‖ ^ 2 = ∑' K : ℤ, ‖c K‖ ^ 2 := by
  have hmem : Memℓp c 2 := memℓp_two_of_summable_norm_sq c hc
  refine ⟨axialDecomposition.symm ⟨c, hmem⟩,
    isHilbertSum_axialLiftL2.hasSum_linearIsometryEquiv_symm ⟨c, hmem⟩, ?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact (hasSum_norm_sq_lp_two (E := fun _ : ℤ => TransverseC3L2) ⟨c, hmem⟩).tsum_eq.symm

/--
The transverse coefficient row stored by the sector lift `axialLiftH2 K b` at its own axial
frequency: the transverse certificate of `b`, rescaled by the weight ratio
`productH2Weight n K / transverseH2Weight n`.
-/
def axialLiftH2CertificateRow (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    TransverseScalarFourierL2 :=
  fixedKRatioCoeffMap K (transverseH2WeightedCoeffs b i)

/-- The certificate of a sector lift is supported at the single axial frequency of its sector,
where it is `axialLiftH2CertificateRow`. -/
theorem productH2WeightedCoeffs_axialLiftH2_eq_single (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    productH2WeightedCoeffs (axialLiftH2 K b) i
      = lp.single 2 K (axialLiftH2CertificateRow K b i) :=
  rfl

/-- Insertion at one axial frequency is an `ℓ²` isometry, so the stored row has the norm of the
component of the certificate it generates. -/
theorem norm_axialLiftH2CertificateRow (K : ℤ) (b : TransverseC3H2) (i : Fin 3) :
    ‖axialLiftH2CertificateRow K b i‖ = ‖productH2WeightedCoeffs (axialLiftH2 K b) i‖ := by
  rw [productH2WeightedCoeffs_axialLiftH2_eq_single]
  exact (lp.norm_single (E := fun _ : ℤ => TransverseScalarFourierL2) (p := 2)
    (by norm_num) K _).symm

/-- The physical field underlying a sector lift is the `L²` axial lift of the physical field of
the amplitude. -/
theorem productH2Embedding_axialLiftH2_eq_axialLiftL2 (K : ℤ) (b : TransverseC3H2) :
    productH2Embedding (axialLiftH2 K b) = axialLiftL2 K (transverseH2Embedding b) :=
  rfl

/--
**Summing the certificates.**  If the lifts of a family of transverse amplitudes are
square-summable in the graph norm, then their stored certificates sum in
`WeightedProductC3Coeffs`, and the squared norms of the summands sum to the squared norm of the
sum.  Each component is an `ℓ²` vector over the axial frequencies whose `K`-th entry is
`axialLiftH2CertificateRow K (b K) i`, and `lp.hasSum_single` is the convergence statement.
-/
theorem exists_hasSum_productH2WeightedCoeffs_axialLiftH2 (b : ℤ → TransverseC3H2)
    (hb : Summable fun K : ℤ => ‖axialLiftH2 K (b K)‖ ^ 2) :
    ∃ a : WeightedProductC3Coeffs,
      HasSum (fun K : ℤ => productH2WeightedCoeffs (axialLiftH2 K (b K))) a ∧
      HasSum (fun K : ℤ => ‖productH2WeightedCoeffs (axialLiftH2 K (b K))‖ ^ 2) (‖a‖ ^ 2) := by
  have hrow : ∀ i : Fin 3, Summable fun K : ℤ => ‖axialLiftH2CertificateRow K (b K) i‖ ^ 2 := by
    intro i
    refine hb.of_nonneg_of_le (fun K => by positivity) fun K => ?_
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    rw [norm_axialLiftH2CertificateRow]
    exact (PiLp.norm_apply_le _ i).trans (norm_productH2WeightedCoeffs_le _)
  set cRow : Fin 3 → ProductScalarFourierL2 := fun i =>
    ⟨fun K => axialLiftH2CertificateRow K (b K) i,
      memℓp_two_of_summable_norm_sq _ (hrow i)⟩ with hcRow
  refine ⟨WithLp.toLp 2 cRow, ?_, ?_⟩
  · have hcomp : HasSum (fun K : ℤ => (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Fin 3 => ProductScalarFourierL2))
          (productH2WeightedCoeffs (axialLiftH2 K (b K))))
        ((PiLp.continuousLinearEquiv 2 ℂ
          (fun _ : Fin 3 => ProductScalarFourierL2)) (WithLp.toLp 2 cRow)) := by
      rw [Pi.hasSum]
      intro i
      have h := lp.hasSum_single (E := fun _ : ℤ => TransverseScalarFourierL2)
        (p := 2) (by simp) (cRow i)
      exact h.congr_fun fun K => (productH2WeightedCoeffs_axialLiftH2_eq_single K (b K) i).symm
    have h2 := hcomp.map (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 => ProductScalarFourierL2)).symm.toContinuousLinearMap
      (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Fin 3 => ProductScalarFourierL2)).symm.continuous
    simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using h2
  · have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i K => ‖(cRow i : ℤ → TransverseScalarFourierL2) K‖ ^ 2)
      (a := fun i => ‖cRow i‖ ^ 2)
      (fun i _ => hasSum_norm_sq_lp_two (E := fun _ : ℤ => TransverseScalarFourierL2) (cRow i))
    rw [show ‖(WithLp.toLp 2 cRow : WeightedProductC3Coeffs)‖ ^ 2
        = ∑ i : Fin 3, ‖cRow i‖ ^ 2 from PiLp.norm_sq_eq_of_L2 _ _]
    refine hsum.congr_fun fun K => ?_
    rw [show ‖productH2WeightedCoeffs (axialLiftH2 K (b K))‖ ^ 2
        = ∑ i : Fin 3, ‖productH2WeightedCoeffs (axialLiftH2 K (b K)) i‖ ^ 2 from
      PiLp.norm_sq_eq_of_L2 _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← norm_axialLiftH2CertificateRow]

/--
**Square-summable families of axial sectors sum in the graph norm.**  If the lifts
`axialLiftH2 K (b K)` of an arbitrary family of transverse `H²` amplitudes have
square-summable graph norms, then the family is summable in `ProductC3H2` and its sum obeys
the Bessel-type bound `‖B‖² ≤ ∑ ‖axialLiftH2 K (b K)‖²`.

Both components converge separately — the physical fields by orthogonality of the axial
sectors, the certificates by disjointness of their axial supports — and the limit pair lies in
the graph because `productH2Submodule` is closed.  This is the summation principle the
resolvent assembly runs on; it assumes nothing about `b` beyond square summability.
-/
theorem exists_hasSum_axialLiftH2_of_summable_norm_sq (b : ℤ → TransverseC3H2)
    (hb : Summable fun K : ℤ => ‖axialLiftH2 K (b K)‖ ^ 2) :
    ∃ B : ProductC3H2, HasSum (fun K : ℤ => axialLiftH2 K (b K)) B ∧
      ‖B‖ ^ 2 ≤ ∑' K : ℤ, ‖axialLiftH2 K (b K)‖ ^ 2 := by
  have hphysle : ∀ K : ℤ, ‖transverseH2Embedding (b K)‖ ^ 2 ≤ ‖axialLiftH2 K (b K)‖ ^ 2 := by
    intro K
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖transverseH2Embedding (b K)‖
        = ‖productH2Embedding (axialLiftH2 K (b K))‖ := by
          rw [productH2Embedding_axialLiftH2_eq_axialLiftL2, (axialLiftL2 K).norm_map]
      _ ≤ ‖axialLiftH2 K (b K)‖ := norm_productH2Embedding_le _
  have hphyssum : Summable fun K : ℤ => ‖transverseH2Embedding (b K)‖ ^ 2 :=
    hb.of_nonneg_of_le (fun K => by positivity) hphysle
  obtain ⟨V, hV, hVnorm⟩ := exists_hasSum_axialLiftL2 _ hphyssum
  obtain ⟨a, ha, hanorm⟩ := exists_hasSum_productH2WeightedCoeffs_axialLiftH2 b hb
  have hVsum : HasSum (fun K : ℤ => productH2Embedding (axialLiftH2 K (b K))) V :=
    hV.congr_fun fun K => (productH2Embedding_axialLiftH2_eq_axialLiftL2 K (b K)).symm
  have hpair : HasSum (fun K : ℤ =>
      ((axialLiftH2 K (b K) : ProductC3H2) : ProductC3L2 × WeightedProductC3Coeffs)) (V, a) :=
    hVsum.prodMk ha
  have hmemB : ((V, a) : ProductC3L2 × WeightedProductC3Coeffs) ∈ productH2Submodule := by
    refine isClosed_productH2Submodule.mem_of_tendsto hpair ?_
    filter_upwards with s
    rw [← AddSubmonoidClass.coe_finsetSum]
    exact (∑ K ∈ s, axialLiftH2 K (b K)).2
  refine ⟨⟨(V, a), hmemB⟩, ?_, ?_⟩
  · refine tendsto_subtype_rng.mpr (hpair.congr fun s => ?_)
    rw [AddSubmonoidClass.coe_finsetSum]
  · have hVle : ‖V‖ ^ 2 ≤ ∑' K : ℤ, ‖axialLiftH2 K (b K)‖ ^ 2 := by
      rw [hVnorm]
      exact hphyssum.tsum_le_tsum hphysle hb
    have hale : ‖a‖ ^ 2 ≤ ∑' K : ℤ, ‖axialLiftH2 K (b K)‖ ^ 2 := by
      refine hasSum_le (fun K => ?_) hanorm hb.hasSum
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_productH2WeightedCoeffs_le _) 2
    have hnormB : ‖(⟨(V, a), hmemB⟩ : ProductC3H2)‖ = max ‖V‖ ‖a‖ := Prod.norm_def _
    rcases max_choice ‖V‖ ‖a‖ with h | h <;> rw [hnormB, h]
    · exact hVle
    · exact hale

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-! ## The sector resolvents -/

/--
**The resolvent of the reduced operator in the `K`-th axial sector.**  This is the
domain-valued inverse carried by `reducedInductionHilleYosidaRay u hu ε hε K`, whose spectral
set is the whole coercive half-plane `{Re z > M_u}`; outside that half-plane it is whatever the
underlying certificate stores and is never used.
-/
def sectorResolventInv (K : ℤ) (z : ℂ) : TransverseC3L2 →L[ℂ] TransverseC3H2 :=
  (reducedInductionHilleYosidaRay u hu ε hε K).resolvent.inv z

/-- **The sector Hille–Yosida bound**, read on the physical field: on the coercive half-plane
`‖ι R_K(z) x‖ ≤ (Re z - M_u)⁻¹ ‖x‖`, uniformly in the axial frequency. -/
theorem norm_transverseH2Embedding_sectorResolventInv_le (K : ℤ) {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : TransverseC3L2) :
    ‖transverseH2Embedding (sectorResolventInv u hu hε K z x)‖
      ≤ (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ * ‖x‖ := by
  change ‖(reducedInductionHilleYosidaRay u hu ε hε K).resolvent.stateResolvent z x‖ ≤ _
  exact le_trans (ContinuousLinearMap.le_opNorm _ _)
    (mul_le_mul_of_nonneg_right
      (norm_stateResolvent_reducedInductionOperator_rightHalfPlane_le u hu ε hε K hz)
      (norm_nonneg _))

/-- `A_{ε,K} R_K(z) = z ι R_K(z) - 1`: the reduced action of a sector resolvent value, from the
right inverse equation. -/
theorem reducedInductionAction_sectorResolventInv (K : ℤ) {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : TransverseC3L2) :
    reducedInductionAction u ε K (sectorResolventInv u hu hε K z x)
      = z • transverseH2Embedding (sectorResolventInv u hu hε K z x) - x := by
  have h := DFunLike.congr_fun
    (op_comp_inv (reducedInductionHilleYosidaRay u hu ε hε K).resolvent
      (show z ∈ (reducedInductionHilleYosidaRay u hu ε hε K).spectralSet from hz)) x
  simp only [ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply] at h
  exact h

/--
**The uniform sector bound.**  At a point of the coercive half-plane the lifted sector
resolvent values are bounded by a single constant, *independent of the axial frequency*:
`‖axialLiftH2 K (R_K(z) x)‖ ≤ γ ‖x‖`.  The constant combines the uniform graph estimate
`norm_axialLiftH2_le_graph` with the sector Hille–Yosida bound and
`reducedInductionAction_sectorResolventInv`; it is `C ((1 + ‖z‖)(Re z - M_u)⁻¹ + 1)` with `C`
the constant of the uniform elliptic estimate.  Without the uniformity in `K` the assembled
series would not converge in the graph norm, because `axialLiftH2 K` is only
`1 + (2πK)²`-bounded.
-/
theorem exists_bound_norm_axialLiftH2_sectorResolvent {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ (K : ℤ) (x : TransverseC3L2),
      ‖axialLiftH2 K (sectorResolventInv u hu hε K z x)‖ ≤ γ * ‖x‖ := by
  obtain ⟨C, hC, hU⟩ := norm_axialLiftH2_le_graph u hε
  have hre : 0 < z.re - ‖transverseStretchingCoefficient u‖ := sub_pos.mpr hz
  refine ⟨C * ((1 + ‖z‖) * (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ + 1), by positivity,
    fun K x => ?_⟩
  have hemb := norm_transverseH2Embedding_sectorResolventInv_le u hu hε K hz x
  have hact : ‖reducedInductionAction u ε K (sectorResolventInv u hu hε K z x)‖ ≤
      ‖z‖ * ((z.re - ‖transverseStretchingCoefficient u‖)⁻¹ * ‖x‖) + ‖x‖ := by
    rw [reducedInductionAction_sectorResolventInv u hu hε K hz x]
    refine le_trans (norm_sub_le
      (z • transverseH2Embedding (sectorResolventInv u hu hε K z x)) x) ?_
    rw [norm_smul]
    have hmul := mul_le_mul_of_nonneg_left hemb (norm_nonneg z)
    linarith
  refine (hU K (sectorResolventInv u hu hε K z x)).trans ?_
  have hsum : ‖transverseH2Embedding (sectorResolventInv u hu hε K z x)‖ +
      ‖reducedInductionAction u ε K (sectorResolventInv u hu hε K z x)‖ ≤
      ((1 + ‖z‖) * (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ + 1) * ‖x‖ := by
    nlinarith [hemb, hact, norm_nonneg x, norm_nonneg z]
  calc C * (‖transverseH2Embedding (sectorResolventInv u hu hε K z x)‖ +
        ‖reducedInductionAction u ε K (sectorResolventInv u hu hε K z x)‖)
      ≤ C * (((1 + ‖z‖) * (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ + 1) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsum hC.le
    _ = C * ((1 + ‖z‖) * (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ + 1) * ‖x‖ := by ring

/-- The sector contributions to the assembled resolvent are square-summable: the uniform sector
bound turns `∑_K ‖P_K x‖² = ‖x‖²` into square summability in the graph norm. -/
theorem summable_norm_sq_axialLiftH2_sectorResolvent {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : ProductC3L2) :
    Summable fun K : ℤ =>
      ‖axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x))‖ ^ 2 := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_bound_norm_axialLiftH2_sectorResolvent u hu hε hz
  refine Summable.of_nonneg_of_le (fun K => by positivity) (fun K => ?_)
    (((hasSum_norm_sq_axialSector x).summable).mul_left (γ ^ 2))
  calc ‖axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x))‖ ^ 2
      ≤ (γ * ‖axialSectorProjL2 K x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hγ K _) 2
    _ = γ ^ 2 * ‖axialSectorProjL2 K x‖ ^ 2 := by ring

/-- The sector resolvent inverts the reduced pencil from the right. -/
theorem reducedInductionPencil_sectorResolventInv (K : ℤ) {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (y : TransverseC3L2) :
    (reducedInductionOperator u ε K).pencil z (sectorResolventInv u hu hε K z y) = y := by
  have h := DFunLike.congr_fun
    ((reducedInductionHilleYosidaRay u hu ε hε K).resolvent.right_inv z
      (show z ∈ (reducedInductionHilleYosidaRay u hu ε hε K).spectralSet from hz)) y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  exact h

/-- The sector resolvent inverts the reduced pencil from the left. -/
theorem sectorResolventInv_reducedInductionPencil (K : ℤ) {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (b : TransverseC3H2) :
    sectorResolventInv u hu hε K z ((reducedInductionOperator u ε K).pencil z b) = b := by
  have h := DFunLike.congr_fun
    ((reducedInductionHilleYosidaRay u hu ε hε K).resolvent.left_inv z
      (show z ∈ (reducedInductionHilleYosidaRay u hu ε hε K).spectralSet from hz)) b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  exact h

/-! ## The assembled resolvent -/

/-- The value of the assembled resolvent: the sum over the axial frequencies of the lifted
sector resolvent values.  It is meaningful only on the coercive half-plane, where
`hasSum_productResolventValue` shows the series converges. -/
def productResolventValue (z : ℂ) (x : ProductC3L2) : ProductC3H2 :=
  ∑' K : ℤ, axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x))

/-- **The defining convergence.**  On the coercive half-plane the sector series converges in the
graph norm of `ProductC3H2` to `productResolventValue`. -/
theorem hasSum_productResolventValue {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : ProductC3L2) :
    HasSum (fun K : ℤ => axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x)))
      (productResolventValue u hu hε z x) := by
  obtain ⟨B, hB, -⟩ := exists_hasSum_axialLiftH2_of_summable_norm_sq
    (fun K => sectorResolventInv u hu hε K z (axialSectorProjL2 K x))
    (summable_norm_sq_axialLiftH2_sectorResolvent u hu hε hz x)
  change HasSum _ (∑' K : ℤ, _)
  rw [hB.tsum_eq]
  exact hB

/-- The assembled resolvent value is bounded by a constant multiple of its argument: Bessel for
the sector sum, the uniform sector bound for each term, and Parseval for the sector
projections. -/
theorem exists_norm_productResolventValue_le {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    ∃ γ : ℝ, ∀ x : ProductC3L2, ‖productResolventValue u hu hε z x‖ ≤ γ * ‖x‖ := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_bound_norm_axialLiftH2_sectorResolvent u hu hε hz
  refine ⟨γ, fun x => ?_⟩
  obtain ⟨B, hB, hBn⟩ := exists_hasSum_axialLiftH2_of_summable_norm_sq
    (fun K => sectorResolventInv u hu hε K z (axialSectorProjL2 K x))
    (summable_norm_sq_axialLiftH2_sectorResolvent u hu hε hz x)
  have hval : productResolventValue u hu hε z x = B := hB.tsum_eq
  have htail : ∑' K : ℤ,
      ‖axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x))‖ ^ 2
      ≤ γ ^ 2 * ‖x‖ ^ 2 := by
    refine hasSum_le (fun K => ?_)
      (summable_norm_sq_axialLiftH2_sectorResolvent u hu hε hz x).hasSum
      ((hasSum_norm_sq_axialSector x).mul_left (γ ^ 2))
    calc ‖axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x))‖ ^ 2
        ≤ (γ * ‖axialSectorProjL2 K x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hγ K _) 2
      _ = γ ^ 2 * ‖axialSectorProjL2 K x‖ ^ 2 := by ring
  have hsq : ‖productResolventValue u hu hε z x‖ ^ 2 ≤ (γ * ‖x‖) ^ 2 := by
    rw [hval]
    calc ‖B‖ ^ 2 ≤ _ := hBn
      _ ≤ γ ^ 2 * ‖x‖ ^ 2 := htail
      _ = (γ * ‖x‖) ^ 2 := by ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-- The assembled resolvent is linear at every point of the coercive half-plane: additivity and
homogeneity are inherited from the summands through uniqueness of sums. -/
def productResolventLinearMap {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) : ProductC3L2 →ₗ[ℂ] ProductC3H2 where
  toFun := productResolventValue u hu hε z
  map_add' x y := by
    refine (hasSum_productResolventValue u hu hε hz (x + y)).unique ?_
    refine ((hasSum_productResolventValue u hu hε hz x).add
      (hasSum_productResolventValue u hu hε hz y)).congr_fun fun K => ?_
    simp
  map_smul' c x := by
    refine (hasSum_productResolventValue u hu hε hz (c • x)).unique ?_
    refine ((hasSum_productResolventValue u hu hε hz x).const_smul c).congr_fun fun K => ?_
    simp

/--
**The assembled domain-valued inverse of the all-frequency pencil.**  On the coercive
half-plane it is the sum of the lifted sector resolvents; off it, the junk value `0` (no
inverse equation is claimed there).
-/
def productResolventInv (z : ℂ) : ProductC3L2 →L[ℂ] ProductC3H2 :=
  if hz : ‖transverseStretchingCoefficient u‖ < z.re then
    (productResolventLinearMap u hu hε hz).mkContinuousOfExistsBound
      (exists_norm_productResolventValue_le u hu hε hz)
  else 0

/-- On the coercive half-plane the assembled inverse is the sector sum. -/
theorem productResolventInv_apply {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : ProductC3L2) :
    productResolventInv u hu hε z x = productResolventValue u hu hε z x := by
  rw [productResolventInv, dite_eq_left hz]
  rfl

/-- **The defining convergence of the assembled inverse.** -/
theorem hasSum_productResolventInv {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : ProductC3L2) :
    HasSum (fun K : ℤ => axialLiftH2 K (sectorResolventInv u hu hε K z (axialSectorProjL2 K x)))
      (productResolventInv u hu hε z x) := by
  rw [productResolventInv_apply u hu hε hz]
  exact hasSum_productResolventValue u hu hε hz x

/-- **The sector data of the assembled inverse.**  Projecting the sum back onto the `K`-th
sector recovers the `K`-th sector resolvent value: every other summand is annihilated by
`axialSectorProjH2 K`. -/
theorem axialSectorProjH2_productResolventInv {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (K : ℤ) (x : ProductC3L2) :
    axialSectorProjH2 K (productResolventInv u hu hε z x)
      = sectorResolventInv u hu hε K z (axialSectorProjL2 K x) := by
  have h := (hasSum_productResolventInv u hu hε hz x).mapL (axialSectorProjH2 K)
  have h2 : HasSum (fun k : ℤ =>
      if k = K then sectorResolventInv u hu hε K z (axialSectorProjL2 K x) else 0)
      (axialSectorProjH2 K (productResolventInv u hu hε z x)) := by
    refine h.congr_fun fun k => ?_
    rw [axialSectorProjH2_axialLiftH2]
    by_cases hk : k = K
    · subst hk; simp
    · simp [hk]
  exact h2.unique (hasSum_ite_eq K _)

/-! ## The two inverse equations -/

/-- **Right inverse.**  Applying the pencil to the assembled sum returns the sector expansion of
the argument, which sums back to it. -/
theorem productInductionPencil_productResolventInv {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : ProductC3L2) :
    (productInductionOperator u ε).pencil z (productResolventInv u hu hε z x) = x := by
  have h := (hasSum_productResolventInv u hu hε hz x).mapL
    ((productInductionOperator u ε).pencil z)
  refine HasSum.unique ?_ (hasSum_axialLiftL2_axialSectorProjL2 x)
  refine h.congr_fun fun K => ?_
  rw [productInductionPencil_axialLiftH2_eq_axialLiftL2,
    reducedInductionPencil_sectorResolventInv u hu hε K hz]

/-- **Left inverse.**  The `K`-th sector of `(z - A) B` is the reduced pencil of the `K`-th
sector of `B`, so the assembled sum reproduces the graph-norm sector expansion of `B`. -/
theorem productResolventInv_productInductionPencil {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (B : ProductC3H2) :
    productResolventInv u hu hε z ((productInductionOperator u ε).pencil z B) = B := by
  have h := hasSum_productResolventInv u hu hε hz ((productInductionOperator u ε).pencil z B)
  refine HasSum.unique ?_ (hasSum_axialLiftH2_axialSectorProjH2 B)
  refine h.congr_fun fun K => ?_
  rw [axialSectorProjL2_productInductionPencil,
    sectorResolventInv_reducedInductionPencil u hu hε K hz]

/-- The right inverse equation in operator form. -/
theorem comp_productResolventInv {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    ((productInductionOperator u ε).pencil z).comp (productResolventInv u hu hε z)
      = ContinuousLinearMap.id ℂ ProductC3L2 :=
  ContinuousLinearMap.ext fun x => productInductionPencil_productResolventInv u hu hε hz x

/-- The left inverse equation in operator form. -/
theorem productResolventInv_comp {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    (productResolventInv u hu hε z).comp ((productInductionOperator u ε).pencil z)
      = ContinuousLinearMap.id ℂ ProductC3H2 :=
  ContinuousLinearMap.ext fun B => productResolventInv_productInductionPencil u hu hε hz B

/-! ## The Hille–Yosida bound and the packaged ray -/

/--
**The Hille–Yosida bound for the assembled resolvent**, in pointwise form:
`‖ι (z - A)⁻¹ x‖ ≤ (Re z - M_u)⁻¹ ‖x‖`.  Parseval for the axial decomposition turns the
sectorwise bounds `‖ι R_K(z) P_K x‖ ≤ (Re z - M_u)⁻¹ ‖P_K x‖` into the same bound for the sum,
because `∑_K ‖P_K x‖² = ‖x‖²`.  The constant is the sector constant: assembling the sectors
does not degrade it.
-/
theorem norm_productH2Embedding_productResolventInv_le {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) (x : ProductC3L2) :
    ‖productH2Embedding (productResolventInv u hu hε z x)‖
      ≤ (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ * ‖x‖ := by
  have hre : 0 < z.re - ‖transverseStretchingCoefficient u‖ := sub_pos.mpr hz
  have hsec : ∀ K : ℤ,
      ‖axialSectorProjL2 K (productH2Embedding (productResolventInv u hu hε z x))‖ ^ 2
        ≤ ((z.re - ‖transverseStretchingCoefficient u‖)⁻¹) ^ 2
            * ‖axialSectorProjL2 K x‖ ^ 2 := by
    intro K
    have hrw : axialSectorProjL2 K (productH2Embedding (productResolventInv u hu hε z x))
        = transverseH2Embedding (sectorResolventInv u hu hε K z (axialSectorProjL2 K x)) := by
      rw [← transverseH2Embedding_axialSectorProjH2,
        axialSectorProjH2_productResolventInv u hu hε hz]
    rw [hrw]
    calc ‖transverseH2Embedding (sectorResolventInv u hu hε K z (axialSectorProjL2 K x))‖ ^ 2
        ≤ ((z.re - ‖transverseStretchingCoefficient u‖)⁻¹ * ‖axialSectorProjL2 K x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (norm_transverseH2Embedding_sectorResolventInv_le u hu hε K hz _) 2
      _ = _ := by ring
  have hsq : ‖productH2Embedding (productResolventInv u hu hε z x)‖ ^ 2
      ≤ ((z.re - ‖transverseStretchingCoefficient u‖)⁻¹ * ‖x‖) ^ 2 := by
    have h := hasSum_le hsec
      (hasSum_norm_sq_axialSector (productH2Embedding (productResolventInv u hu hε z x)))
      ((hasSum_norm_sq_axialSector x).mul_left
        (((z.re - ‖transverseStretchingCoefficient u‖)⁻¹) ^ 2))
    calc ‖productH2Embedding (productResolventInv u hu hε z x)‖ ^ 2
        ≤ ((z.re - ‖transverseStretchingCoefficient u‖)⁻¹) ^ 2 * ‖x‖ ^ 2 := h
      _ = _ := by ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/--
**An auxiliary propagated certificate.**  Every point of the coercive right half-plane
`{Re z > M_u}` carries the two-sided inverse `productResolventInv u hu hε z`, so the
repository's rational propagation construction
`DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses` — the same one used for the reduced
operator in `FastDynamo/Global/ReducedInductionHalfPlaneResolvent.lean` — bundles them into a
`HasResolventOn` certificate whose inverse is continuous on the half-plane.  Its stored inverse
is the rational propagation of the base inverse at `M_u + 1` rather than the sector sum, but
`productResolventPropagated_inv` identifies the two; this certificate exists only to transport
that continuity to `productResolventInv` itself.
-/
def productResolventPropagated :
    HasResolventOn (productInductionOperator u ε)
      {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re} :=
  DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses
    (productInductionOperator u ε)
    (((‖transverseStretchingCoefficient u‖ + 1 : ℝ) : ℂ))
    (productResolventInv u hu hε (((‖transverseStretchingCoefficient u‖ + 1 : ℝ) : ℂ)))
    (productResolventInv_comp u hu hε (by simp))
    (comp_productResolventInv u hu hε (by simp))
    {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re}
    (fun z hz => ⟨productResolventInv u hu hε z,
      productResolventInv_comp u hu hε hz, comp_productResolventInv u hu hε hz⟩)

/-- The inverse stored by the propagated certificate is the assembled sector sum: two-sided
inverses of the same pencil agree. -/
theorem productResolventPropagated_inv {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    (productResolventPropagated u hu hε).inv z = productResolventInv u hu hε z := by
  set h := productResolventPropagated u hu hε with hdef
  calc h.inv z
      = (h.inv z).comp
          (((productInductionOperator u ε).pencil z).comp
            (productResolventInv u hu hε z)) := by
        rw [comp_productResolventInv u hu hε hz, ContinuousLinearMap.comp_id]
    _ = ((h.inv z).comp ((productInductionOperator u ε).pencil z)).comp
          (productResolventInv u hu hε z) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = productResolventInv u hu hε z := by
        rw [h.left_inv z hz, ContinuousLinearMap.id_comp]

/-- **Continuity of the assembled resolvent** on the coercive half-plane, transported from the
propagated certificate through `productResolventPropagated_inv`. -/
theorem continuousOn_productResolventInv :
    ContinuousOn (productResolventInv u hu hε)
      {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re} :=
  (productResolventPropagated u hu hε).continuousOn.congr
    (fun _z hz => (productResolventPropagated_inv u hu hε hz).symm)

/--
**The half-plane resolvent of the all-frequency induction operator.**  Its inverse is the
assembled sector sum `productResolventInv u hu hε`: the two inverse equations hold sector by
sector, and the continuity is `continuousOn_productResolventInv`.
-/
def productInductionHalfPlaneResolvent :
    HasResolventOn (productInductionOperator u ε)
      {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re} where
  inv := productResolventInv u hu hε
  left_inv := fun _z hz => productResolventInv_comp u hu hε hz
  right_inv := fun _z hz => comp_productResolventInv u hu hε hz
  continuousOn := continuousOn_productResolventInv u hu hε

/-- **The Hille–Yosida bound on the half-plane**: `‖(z - A)⁻¹‖ ≤ (Re z - M_u)⁻¹`, with the same
constant `M_u = ‖∇⊥ u‖_∞` as in every axial sector. -/
theorem norm_stateResolvent_productInduction_le {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    ‖(productInductionHalfPlaneResolvent u hu hε).stateResolvent z‖
      ≤ (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ := by
  have hre : 0 < z.re - ‖transverseStretchingCoefficient u‖ := sub_pos.mpr hz
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  exact norm_productH2Embedding_productResolventInv_le u hu hε hz x

/--
**The Hille–Yosida ray of the all-frequency induction operator.**  For a transversely
divergence-free `W^{1,∞}` velocity and a positive diffusivity, the operator
`A = productInductionOperator u ε` has a two-sided domain-valued resolvent at every `z` with
`Re z > M_u := ‖transverseStretchingCoefficient u‖`, obeying `‖(z - A)⁻¹‖ ≤ (Re z - M_u)⁻¹`.

This is the single input of the abstract generation theorem: together with
`denseRange_productInductionOperator_embedding` it produces the `C₀`-semigroup of the
induction operator on `ProductC3L2` and a realization of `A` as its generator.  The constant is
the fixed-sector one, uniform in `ε` and in the axial frequency.
-/
def productHilleYosidaRay :
    HilleYosidaRay (productInductionOperator u ε) ‖transverseStretchingCoefficient u‖ :=
  HilleYosidaRay.ofHalfPlane (productInductionHalfPlaneResolvent u hu hε)
    (fun _z hz => norm_stateResolvent_productInduction_le u hu hε hz)

end

end FastDynamo
