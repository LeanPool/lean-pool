/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.StationaryCarrierTransport

/-!
# ShellSumScaledTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transporting the stationary potential projection along a *dilating* factor map

`StationaryCarrierTransport.lean` transports the stationary potential projection
along a factor map that is *equivariant*: `Φ (x +ᵥ ω) = x +ᵥ Φ ω`.  The per-layer
transport of `e.perturb.assumption` is carried by a map that is equivariant only
after a **dilation of the acting group**:

`Ψ (x +ᵥ ω) = (c • x) +ᵥ Ψ ω`,  `c = 3^k`,

because the layer-`k` field is the layer-`0` field dilated by `3^{-k}` (and
rescaled by `3^{γ k}`), and a dilation conjugates translations rather than
commuting with them.

This module generalizes the intertwining argument to that situation.  The point
is that the stationary potential subspace does **not** change when the acting
group is rescaled by a nonzero constant: rescaling the action rescales every
horizontal gradient by the same constant, and `horizontalGradientRange` is a
*submodule*, hence invariant under nonzero scalars.  So the conclusion is
identical to the unscaled one.

## Main results

* `hasHorizontalGradient_of_intertwine_smul` — a bounded pair of maps
  intertwining the two translation actions **up to the dilation `c`** carries a
  horizontal gradient to `c •` a horizontal gradient.
* `mem_stationaryPotentialSubspace_of_intertwine_smul` — hence preserves the
  stationary potential subspace, for every `c ≠ 0`.
* `carrierTransport_koopman_smul`, `carrierTransportAdj_koopman_smul` — the
  Koopman intertwining of a dilating factor map and of its Hilbert adjoint.
* `stationaryPotentialProjection_carrierTransport_smul`,
  `norm_stationaryPotentialProjection_carrierTransport_smul` — the naturality of
  the projection and the equality of the two projected energies along a
  dilating factor map.
-/

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Probability.Stationary

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### Horizontal gradients under a dilating intertwiner -/

section Intertwine

variable {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {ν : Measure Ω'}
variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
  [VAddInvariantMeasure (Vec d) Ω μ]
variable [AddAction (Vec d) Ω'] [MeasurableConstVAdd (Vec d) Ω']
  [VAddInvariantMeasure (Vec d) Ω' ν]

/-- **A dilating intertwiner carries horizontal gradients to horizontal
gradients, up to the dilation factor.** -/
theorem hasHorizontalGradient_of_intertwine_smul {c : ℝ}
    {Sscal : ScalarL2 μ →L[ℝ] ScalarL2 ν} {Svec : VectorL2 d μ →L[ℝ] VectorL2 d ν}
    (hcomm : ∀ (x : Vec d) (φ : ScalarL2 μ),
      Sscal (koopman (μ := μ) (d := d) (c • x) φ)
        = koopman (μ := ν) (d := d) x (Sscal φ))
    (hcoord : ∀ (i : Fin d) (F : VectorL2 d μ),
      vectorL2Coord (μ := ν) i (Svec F) = Sscal (vectorL2Coord (μ := μ) i F))
    {φ : ScalarL2 μ} {F : VectorL2 d μ}
    (hφ : HasHorizontalGradient (μ := μ) φ F) :
    HasHorizontalGradient (μ := ν) (Sscal φ) (c • Svec F) := by
  intro i
  have hcoord' : vectorL2Coord (μ := ν) i (c • Svec F)
      = c • Sscal (vectorL2Coord (μ := μ) i F) := by
    rw [map_smul, hcoord i F]
  rw [hcoord']
  have hlin : HasDerivAt (fun t : ℝ => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hscomp : HasDerivAt
      (fun t : ℝ => koopman (μ := μ) (d := d) ((c * t) • (Pi.single i 1 : Vec d)) φ)
      (c • vectorL2Coord (μ := μ) i F) 0 := by
    have hg : HasDerivAt
        (fun s : ℝ => koopman (μ := μ) (d := d) (s • (Pi.single i 1 : Vec d)) φ)
        (vectorL2Coord (μ := μ) i F) (c * 0) := by
      rw [mul_zero]
      exact hφ i
    have h := hg.scomp (0 : ℝ) hlin
    simpa only [Function.comp_def] using h
  have hcomp : (fun t : ℝ =>
        koopman (μ := ν) (d := d) (t • (Pi.single i 1 : Vec d)) (Sscal φ))
      = fun t : ℝ =>
        Sscal (koopman (μ := μ) (d := d) ((c * t) • (Pi.single i 1 : Vec d)) φ) := by
    funext t
    rw [← hcomm (t • (Pi.single i 1 : Vec d)) φ, smul_smul]
  rw [hcomp]
  have hfd := (Sscal.hasFDerivAt (x := koopman (μ := μ) (d := d)
    ((c * (0 : ℝ)) • (Pi.single i 1 : Vec d)) φ)).comp_hasDerivAt 0 hscomp
  simpa only [map_smul] using! hfd

theorem mem_stationaryPotentialSubspace_of_intertwine_smul {c : ℝ} (hc : c ≠ 0)
    {Sscal : ScalarL2 μ →L[ℝ] ScalarL2 ν} {Svec : VectorL2 d μ →L[ℝ] VectorL2 d ν}
    (hcomm : ∀ (x : Vec d) (φ : ScalarL2 μ),
      Sscal (koopman (μ := μ) (d := d) (c • x) φ)
        = koopman (μ := ν) (d := d) x (Sscal φ))
    (hcoord : ∀ (i : Fin d) (F : VectorL2 d μ),
      vectorL2Coord (μ := ν) i (Svec F) = Sscal (vectorL2Coord (μ := μ) i F))
    {F : VectorL2 d μ} (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    Svec F ∈ stationaryPotentialSubspace (μ := ν) (d := d) := by
  have hsub : horizontalGradientRange (μ := μ) (d := d) ≤
      Submodule.comap (Svec : VectorL2 d μ →ₗ[ℝ] VectorL2 d ν)
        (stationaryPotentialSubspace (μ := ν) (d := d)) := by
    intro G hG
    obtain ⟨ψ, hψ⟩ := hG
    have hmemc : c • Svec G ∈ stationaryPotentialSubspace (μ := ν) (d := d) :=
      Submodule.le_topologicalClosure _
        ⟨Sscal ψ, hasHorizontalGradient_of_intertwine_smul hcomm hcoord hψ⟩
    have hrewrite : Svec G = c⁻¹ • (c • Svec G) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    change Svec G ∈ stationaryPotentialSubspace (μ := ν) (d := d)
    rw [hrewrite]
    exact (stationaryPotentialSubspace (μ := ν) (d := d)).smul_mem _ hmemc
  have hclosed : IsClosed
      ((Submodule.comap (Svec : VectorL2 d μ →ₗ[ℝ] VectorL2 d ν)
        (stationaryPotentialSubspace (μ := ν) (d := d))) : Set (VectorL2 d μ)) :=
    (Submodule.isClosed_topologicalClosure _).preimage Svec.continuous
  exact Submodule.topologicalClosure_minimal _ hsub hclosed hF

end Intertwine

/-! ### The transport along a dilating factor map -/

section Transport

variable {d : ℕ} {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
variable [AddAction (Vec d) Ω₁] [MeasurableConstVAdd (Vec d) Ω₁]
  [VAddInvariantMeasure (Vec d) Ω₁ μ₁]
variable [AddAction (Vec d) Ω₂] [MeasurableConstVAdd (Vec d) Ω₂]
  [VAddInvariantMeasure (Vec d) Ω₂ μ₂]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Φ : Ω₂ → Ω₁} {c : ℝ}

/-- The transport of a dilating factor map intertwines the two Koopman families
with the group dilated by `c`. -/
theorem carrierTransport_koopman_smul (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = (c • x) +ᵥ Φ ω)
    (x : Vec d) (g : Lp E 2 μ₁) :
    carrierTransport E hΦ (koopman (μ := μ₁) (d := d) (c • x) g)
      = koopman (μ := μ₂) (d := d) x (carrierTransport E hΦ g) := by
  have hvadd : MeasurePreserving (fun ω : Ω₂ => x +ᵥ ω) μ₂ μ₂ :=
    measurePreserving_const_vadd (μ := μ₂) x
  have h₁ : (carrierTransport E hΦ (koopman (μ := μ₁) (d := d) (c • x) g) : Ω₂ → E)
      =ᵐ[μ₂] fun ω => (g : Ω₁ → E) ((c • x) +ᵥ Φ ω) := by
    refine (coeFn_carrierTransport hΦ _).trans ?_
    have hg : (koopman (μ := μ₁) (d := d) (c • x) g : Ω₁ → E)
        =ᵐ[μ₁] fun ω => (g : Ω₁ → E) ((c • x) +ᵥ ω) :=
      Lp.coeFn_compMeasurePreserving _ (measurePreserving_const_vadd (μ := μ₁) (c • x))
    exact hg.comp_tendsto hΦ.quasiMeasurePreserving.tendsto_ae
  have h₂ : (koopman (μ := μ₂) (d := d) x (carrierTransport E hΦ g) : Ω₂ → E)
      =ᵐ[μ₂] fun ω => (g : Ω₁ → E) ((c • x) +ᵥ Φ ω) := by
    refine (Lp.coeFn_compMeasurePreserving _ hvadd).trans ?_
    have hstep := (coeFn_carrierTransport hΦ g).comp_tendsto
      hvadd.quasiMeasurePreserving.tendsto_ae
    refine hstep.trans (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg (g : Ω₁ → E) (hequiv x ω)
  exact Lp.ext (h₁.trans h₂.symm)

/-- **The adjoint of a dilating transport intertwines the Koopman families in
the opposite direction**: it turns a translation by `y` on `Ω₂` into a
translation by `c • y` on `Ω₁`. -/
theorem carrierTransportAdj_koopman_smul [CompleteSpace E]
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = (c • x) +ᵥ Φ ω)
    (y : Vec d) (w : Lp E 2 μ₂) :
    carrierTransportAdj E hΦ (koopman (μ := μ₂) (d := d) y w)
      = koopman (μ := μ₁) (d := d) (c • y) (carrierTransportAdj E hΦ w) := by
  refine ext_inner_right ℝ fun v => ?_
  have hz : -(c • (-y)) = c • y := by rw [smul_neg, neg_neg]
  calc (inner ℝ (carrierTransportAdj E hΦ (koopman (μ := μ₂) (d := d) y w)) v : ℝ)
      = inner ℝ (koopman (μ := μ₂) (d := d) y w) (carrierTransport E hΦ v) :=
        inner_carrierTransportAdj_left hΦ _ _
    _ = inner ℝ w (koopman (μ := μ₂) (d := d) (-y) (carrierTransport E hΦ v)) :=
        inner_koopman_left y w _
    _ = inner ℝ w (carrierTransport E hΦ
          (koopman (μ := μ₁) (d := d) (c • (-y)) v)) := by
        rw [carrierTransport_koopman_smul hΦ hequiv (-y) v]
    _ = inner ℝ (carrierTransportAdj E hΦ w)
          (koopman (μ := μ₁) (d := d) (c • (-y)) v) :=
        (inner_carrierTransportAdj_left hΦ _ _).symm
    _ = inner ℝ (koopman (μ := μ₁) (d := d) (-(c • (-y)))
          (carrierTransportAdj E hΦ w)) v := by
        rw [inner_koopman_left (-(c • (-y))) _ v, neg_neg]
    _ = inner ℝ (koopman (μ := μ₁) (d := d) (c • y)
          (carrierTransportAdj E hΦ w)) v := by
        rw [hz]

/-! ### Both directions preserve the stationary potential subspace -/

theorem mem_stationaryPotentialSubspace_carrierTransport_smul (hc : c ≠ 0)
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = (c • x) +ᵥ Φ ω)
    {G : VectorL2 d μ₁} (hG : G ∈ stationaryPotentialSubspace (μ := μ₁) (d := d)) :
    carrierTransport (HilbertVec d) hΦ G ∈
      stationaryPotentialSubspace (μ := μ₂) (d := d) :=
  mem_stationaryPotentialSubspace_of_intertwine_smul hc
    (Sscal := carrierTransport ℝ hΦ) (Svec := carrierTransport (HilbertVec d) hΦ)
    (fun x φ => carrierTransport_koopman_smul hΦ hequiv x φ)
    (fun i G' => vectorL2Coord_carrierTransport hΦ i G') hG

theorem mem_stationaryPotentialSubspace_carrierTransportAdj_smul (hc : c ≠ 0)
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = (c • x) +ᵥ Φ ω)
    {G : VectorL2 d μ₂} (hG : G ∈ stationaryPotentialSubspace (μ := μ₂) (d := d)) :
    carrierTransportAdj (HilbertVec d) hΦ G ∈
      stationaryPotentialSubspace (μ := μ₁) (d := d) := by
  refine mem_stationaryPotentialSubspace_of_intertwine_smul (inv_ne_zero hc)
    (Sscal := carrierTransportAdj ℝ hΦ)
    (Svec := carrierTransportAdj (HilbertVec d) hΦ) (fun x φ => ?_)
    (fun i G' => vectorL2Coord_carrierTransportAdj hΦ i G') hG
  rw [carrierTransportAdj_koopman_smul hΦ hequiv (c⁻¹ • x) φ, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

/-! ### Naturality of the projection along a dilating factor map -/

/-- **The stationary potential projection is natural under a dilating
equivariant factor map.**  The dilation of the acting group does not change the
subspace, so the conclusion is verbatim the unscaled one. -/
theorem stationaryPotentialProjection_carrierTransport_smul (hc : c ≠ 0)
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = (c • x) +ᵥ Φ ω)
    (G : VectorL2 d μ₁) :
    stationaryPotentialProjection (μ := μ₂)
        (carrierTransport (HilbertVec d) hΦ G)
      = carrierTransport (HilbertVec d) hΦ
          (stationaryPotentialProjection (μ := μ₁) G) := by
  refine (eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    (mem_stationaryPotentialSubspace_carrierTransport_smul hc hΦ hequiv
      (stationaryPotentialProjection_mem (μ := μ₁) G)) ?_).symm
  have hsub : carrierTransport (HilbertVec d) hΦ G
      - carrierTransport (HilbertVec d) hΦ (stationaryPotentialProjection (μ := μ₁) G)
      = carrierTransport (HilbertVec d) hΦ
          (G - stationaryPotentialProjection (μ := μ₁) G) :=
    (map_sub (carrierTransport (HilbertVec d) hΦ) _ _).symm
  rw [hsub, stationarySolenoidalSubspace, Submodule.mem_orthogonal]
  intro v hv
  have hAv : carrierTransportAdj (HilbertVec d) hΦ v ∈
      stationaryPotentialSubspace (μ := μ₁) (d := d) :=
    mem_stationaryPotentialSubspace_carrierTransportAdj_smul hc hΦ hequiv hv
  have hperp := sub_stationaryPotentialProjection_mem_orthogonal (μ := μ₁) G
  rw [stationarySolenoidalSubspace, Submodule.mem_orthogonal] at hperp
  have hzero := hperp _ hAv
  rw [← inner_carrierTransportAdj_left hΦ v
    (G - stationaryPotentialProjection (μ := μ₁) G)]
  exact hzero

/-- **The two projected energies agree along a dilating factor map.** -/
theorem norm_stationaryPotentialProjection_carrierTransport_smul (hc : c ≠ 0)
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = (c • x) +ᵥ Φ ω)
    (G : VectorL2 d μ₁) :
    ‖stationaryPotentialProjection (μ := μ₂) (carrierTransport (HilbertVec d) hΦ G)‖
      = ‖stationaryPotentialProjection (μ := μ₁) G‖ := by
  rw [stationaryPotentialProjection_carrierTransport_smul hc hΦ hequiv G]
  exact norm_carrierTransport hΦ _

end Transport

end

end Algsuperdiff.Section3.Provider.Corrector
