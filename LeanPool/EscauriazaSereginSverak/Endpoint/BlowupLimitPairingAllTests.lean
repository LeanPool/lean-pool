/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitTraceField

/-!
# Smooth momentum pairings on the source cylinder

The local momentum identity gives a time-integral formula for every smooth
spatial pairing with the all-time representative from `lem:weak-cont-L3`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem blowupLimit_pairing_continuity_extends_from_open_interval
    {c : ℝ} (hc : c < 0) {ell pairExt : ℝ → ℝ}
    (hEq : ell =ᵐ[volume.restrict (Ioo c 0)] pairExt)
    (hell : ContinuousOn ell (Icc c 0))
    (hpair : ContinuousOn pairExt (Icc c 0)) :
    EqOn ell pairExt (Icc c 0) := by
  have hopen := Measure.eqOn_open_of_ae_eq hEq isOpen_Ioo
    (hell.mono Ioo_subset_Icc_self)
    (hpair.mono Ioo_subset_Icc_self)
  apply Set.EqOn.of_subset_closure hopen
  · exact hell
  · exact hpair
  · exact Ioo_subset_Icc_self
  · intro t ht
    rw [closure_Ioo hc.ne]
    exact ht

private theorem blowupLimit_scalar_trace_primitive_extends_to_closed_interval
    {c C : ℝ} {ell g : ℝ → ℝ} (hcle : -1 ≤ c) (_hc : c < 0)
    (hell : ContinuousOn ell (Icc (-1 : ℝ) 0)) (hg : Integrable g volume)
    (hAE : ell =ᵐ[volume.restrict (Ioo (-1 : ℝ) 0)]
      (fun t => C + ∫ r in (-1 / 2 : ℝ)..t, g r)) :
    EqOn ell (fun t => C + ∫ r in (-1 / 2 : ℝ)..t, g r) (Icc c 0) := by
  have hprimitiveCont : Continuous (fun t : ℝ => C + ∫ r in (-1 / 2 : ℝ)..t, g r) :=
    continuous_const.add (hg.continuous_primitive (-1 / 2 : ℝ))
  have hopen := Measure.eqOn_open_of_ae_eq hAE isOpen_Ioo
    (hell.mono Ioo_subset_Icc_self) hprimitiveCont.continuousOn
  have hclosed : EqOn ell
      (fun t => C + ∫ r in (-1 / 2 : ℝ)..t, g r) (Icc (-1 : ℝ) 0) := by
    apply Set.EqOn.of_subset_closure hopen
    · exact hell
    · exact hprimitiveCont.continuousOn
    · exact Ioo_subset_Icc_self
    · intro t ht
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
      exact ht
  intro t ht
  apply hclosed
  exact ⟨le_trans hcle ht.1, ht.2⟩

private theorem blowupLimit_momentum_equation_on_representative_ball
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    ∀ Φ : ParabolicPoint → Vec3,
      Φ ∈ spaceTimeTestFunction (V := Vec3) weakContL3SpatialBall (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => Φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z) = 0 := by
  intro Φ hΦ
  have h := hS3 Φ hΦ
  have heq : (fun z : ParabolicPoint =>
      (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => Φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => Φ y i) j z
        - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z
        - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * Φ z i)) =
      fun z => (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
            u z i * u z j * spatialPartial (fun y => Φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Du z i j * spatialPartial (fun y => Φ y i) j z
        - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z) := by
    funext z
    simp
  rw [heq] at h
  simpa only [weakContL3SpatialBall] using h

private theorem blowupLimit_pairing_source_slice_ae
    {u : ParabolicPoint → Vec3}
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (ψ : Vec3 → Vec3) (χ : Vec3 → ℝ)
    (φ : weakContL3SmoothTest)
    (hcut : ∀ x, weakContL3CutoffTest χ φ x = ψ x)
    (hψsupport : tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (hφLp32 : MemLp (fun x => weakContL3VecToLp (ψ x))
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (hvae : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        ∃ hslice : MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x,t))) 3
            (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
          v ⟨t,ht⟩ = hslice.toLp _) :
    ∀ᵐ t ∂volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ x, inner ℝ (v ⟨t, ht⟩ x)
          (hφLp32.toLp (fun x => weakContL3VecToLp (ψ x)) x)
          ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) =
        ∫ x in weakContL3SpatialBall,
          weakContL3MomentumPairing u χ φ (x,t) := by
  filter_upwards [hvae] with t ht
  obtain ⟨htI, hslice, hEq⟩ := ht
  have hEq' : (fun x : Vec3 => v ⟨t, htI⟩ x) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => hslice.toLp _ x) := by
    exact Lp.ext_iff.mp hEq
  have hraw : (fun x : Vec3 => hslice.toLp _ x) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => WithLp.toLp 2 (u (x,t))) := by
    filter_upwards [hslice.coeFn_toLp] with x hx
    exact hx
  have hcomponents : ∀ᵐ x ∂(volume.restrict
      (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
      ∀ i : Fin 3, v ⟨t, htI⟩ x i = u (x,t) i := by
    filter_upwards [hEq', hraw] with x hx₁ hx₂
    intro i
    exact congrArg (fun y : L2Vec3 => y.ofLp i) (hx₁.trans hx₂)
  have hwhole : (fun x : Vec3 =>
      ∑ i : Fin 3, v ⟨t, htI⟩ x i * ψ x i) =ᵐ[
        volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      fun x => weakContL3MomentumPairing u χ φ (x,t) := by
    filter_upwards [hcomponents] with x hx
    simp only [weakContL3MomentumPairing, parabolicHomeomorph_symm_apply,
      hcut]
    congr 1
    funext i
    exact congrArg (fun a : ℝ => a * ψ x i) (hx i)
  have hIntPair : (∫ x, inner ℝ (v ⟨t, htI⟩ x)
      (hφLp32.toLp (fun x => weakContL3VecToLp (ψ x)) x)
      ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) =
      ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v ⟨t, htI⟩ x i * ψ x i := by
    apply integral_congr_ae
    filter_upwards [hφLp32.coeFn_toLp] with x hx₂
    rw [hx₂]
    have hinner : inner ℝ (v ⟨t, htI⟩ x)
        (weakContL3VecToLp (ψ x)) =
        ∑ i : Fin 3, v ⟨t, htI⟩ x i * ψ x i := by
      simp only [weakContL3VecToLp, ContinuousLinearEquiv.coe_coe,
        PiLp.continuousLinearEquiv_symm_apply, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simpa only [weakContL3SpatialBall] using hinner
  have hIntAll : (∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v ⟨t, htI⟩ x i * ψ x i) =
      ∫ x in weakContL3SpatialBall,
        weakContL3MomentumPairing u χ φ (x,t) := by
    have hsubset : vec3Ball (0 : Vec3) (3 / 4 : ℝ) ⊆ weakContL3SpatialBall := by
      intro x hx
      have hxnorm : vec3EuclideanNorm (x - 0) < 3 / 4 := by
        simpa [mem_vec3Ball] using hx
      change vec3EuclideanNorm (x - 0) < 1
      exact lt_trans hxnorm (by norm_num)
    have hzero : ∀ x ∈ weakContL3SpatialBall \ vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        weakContL3MomentumPairing u χ φ (x,t) = 0 := by
      intro x hx
      have hxnot : x ∉ tsupport ψ := fun hmem => hx.2 (hψsupport hmem)
      have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxnot
      simp [weakContL3MomentumPairing, hcut, hψx]
    calc
      ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v ⟨t, htI⟩ x i * ψ x i =
        ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          weakContL3MomentumPairing u χ φ (x,t) := by
            exact integral_congr_ae hwhole
      _ = ∫ x in weakContL3SpatialBall,
          weakContL3MomentumPairing u χ φ (x,t) :=
        (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (isOpen_vec3Ball _ _).measurableSet hsubset hzero).symm
  exact ⟨htI, hIntPair.trans hIntAll⟩

private theorem blowupLimit_closed_pairing_formula
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (χ : Vec3 → ℝ) (ψ : Vec3 → Vec3)
    (φ : weakContL3SmoothTest)
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (wLp : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (ell : ℝ → ℝ) (hcut : ∀ x, weakContL3CutoffTest χ φ x = ψ x)
    (_hψsupport : tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (hpairTest : ∀ τ : Icc (-(3 / 4 : ℝ) ^ 2) 0,
      (∫ x, inner ℝ (v τ x) (wLp x)
        ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) =
      ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v τ x i * ψ x i)
    (hpairCont : Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
      ∫ x, inner ℝ (v t x) (wLp x)
        ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))))
    (hpairEqAE : ∀ᵐ t ∂volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ x, inner ℝ (v ⟨t, ht⟩ x) (wLp x)
          ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) =
        ∫ x in weakContL3SpatialBall,
          weakContL3MomentumPairing u χ φ (x,t))
    (htraceAE : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      (∫ x in weakContL3SpatialBall,
        weakContL3MomentumPairing u χ φ (x,t) ∂volume) = ell t)
    (hellContinuous : Continuous ell)
    (hgInt : IntegrableOn (fun t => ∫ x in weakContL3SpatialBall,
      weakContL3MomentumFlux u Du p χ φ (x,t) ∂volume) (Ioo (-1 : ℝ) 0))
    (hfLoc : LocallyIntegrableOn (fun t => ∫ x in weakContL3SpatialBall,
      weakContL3MomentumPairing u χ φ (x,t) ∂volume) (Ioo (-1 : ℝ) 0))
    (hderiv : HasWeakDerivOn (Ioo (-1 : ℝ) 0)
      (fun t => ∫ x in weakContL3SpatialBall,
        weakContL3MomentumPairing u χ φ (x,t) ∂volume)
      (fun t => ∫ x in weakContL3SpatialBall,
        weakContL3MomentumFlux u Du p χ φ (x,t) ∂volume)) :
    ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
      (∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v t x i * ψ x i) -
      (∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v s x i * ψ x i) =
      ∫ τ in s.1..t.1, ∫ x in vec3Ball (0 : Vec3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (x,τ) i * u (x,τ) j * spatialDeriv (fun y => ψ y i) j x)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          Du (x,τ) i j * spatialDeriv (fun y => ψ y i) j x)
        + p (x,τ) * ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x
        ∂volume := by
  let pairOn (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) : ℝ :=
    ∫ x, inner ℝ (v t x) (wLp x)
      ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))
  let pairExt (t : ℝ) : ℝ := if ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0
      then pairOn ⟨t, ht⟩ else 0
  have hpairOnCont : Continuous pairOn := hpairCont
  have hpairExtCont : ContinuousOn pairExt (Icc (-(3 / 4 : ℝ) ^ 2) 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 => pairExt t)
    have hfun : (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 => pairExt t) = pairOn := by
      funext t
      simp only [pairExt, dite_eq_left t.property]
    rw [hfun]
    exact hpairOnCont
  have hEqOpen : ell =ᵐ[volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)] pairExt := by
    have hsmall : Ioo (-(3 / 4 : ℝ) ^ 2) 0 ⊆ Ioo (-1 : ℝ) 0 := by
      intro t ht
      exact ⟨by linarith only [ht.1], ht.2⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmall htraceAE, hpairEqAE,
      ae_restrict_mem measurableSet_Ioo] with t h₁ h₂ htopen
    obtain ⟨ht, hpair⟩ := h₂
    have hpair' : pairExt t =
        ∫ x in weakContL3SpatialBall,
          weakContL3MomentumPairing u χ φ (x,t) := by
      dsimp [pairExt]
      rw [dite_eq_left ht]
      simpa only [pairOn] using hpair
    exact h₁.symm.trans hpair'.symm
  have htraceEq : EqOn ell pairExt (Icc (-(3 / 4 : ℝ) ^ 2) 0) :=
    blowupLimit_pairing_continuity_extends_from_open_interval
      (by norm_num) hEqOpen hellContinuous.continuousOn hpairExtCont
  let gFlux : ℝ → ℝ := fun t =>
    ∫ x in weakContL3SpatialBall,
      weakContL3MomentumFlux u Du p χ φ (x,t) ∂volume
  let gFull : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator gFlux
  have hgFullInt : Integrable gFull volume := hgInt.integrable_indicator measurableSet_Ioo
  have hderivFull : HasWeakDerivOn (Ioo (-1 : ℝ) 0)
      (fun t => ∫ x in weakContL3SpatialBall,
        weakContL3MomentumPairing u χ φ (x,t) ∂volume) gFull := by
    intro θ hθ
    have hIntEq : (∫ t in Ioo (-1 : ℝ) 0, gFull t * θ t) =
        ∫ t in Ioo (-1 : ℝ) 0, gFlux t * θ t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp [gFull, ht]
    rw [hIntEq]
    exact hderiv θ hθ
  obtain ⟨C, hCraw⟩ := exists_ae_eq_const_add_intervalIntegral_of_weakDeriv
    (a := (-1 : ℝ)) (b := 0) (t₀ := (-1 / 2 : ℝ))
    (by norm_num) (by norm_num) hfLoc
    (hgFullInt.locallyIntegrable.locallyIntegrableOn (Ioo (-1 : ℝ) 0)) hderivFull
  have hellPrimitiveAE : ell =ᵐ[volume.restrict (Ioo (-1 : ℝ) 0)]
      (fun t => C + ∫ r in (-1 / 2 : ℝ)..t, gFull r) := by
    filter_upwards [htraceAE, ae_restrict_of_ae hCraw,
      ae_restrict_mem measurableSet_Ioo] with t hEll hRaw ht
    exact hEll.symm.trans (hRaw ht)
  have hprimitiveIcc := blowupLimit_scalar_trace_primitive_extends_to_closed_interval
    (c := -(3 / 4 : ℝ) ^ 2)
    (by norm_num) (by norm_num) hellContinuous.continuousOn hgFullInt hellPrimitiveAE
  intro s t
  have hst : s.1 ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := s.2
  have htt : t.1 ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := t.2
  have hIntBetween (a b : ℝ)
      (ha : a ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0)
      (hb : b ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      (∫ r in a..b, gFull r) = ∫ r in a..b, gFlux r := by
    apply intervalIntegral.integral_congr_uIoo
    intro r hr
    change min a b < r ∧ r < max a b at hr
    have hmin : -(3 / 4 : ℝ) ^ 2 ≤ min a b := le_min ha.1 hb.1
    have hmax : max a b ≤ 0 := max_le ha.2 hb.2
    have hrlo : -1 < r := by linarith only [hmin, hr.1]
    have hrhi : r < 0 := by linarith only [hr.2, hmax]
    simp [gFull, gFlux, hrlo, hrhi]
  have hformula (τ : ℝ) (hτ : τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      (∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v ⟨τ, hτ⟩ x i * ψ x i) = C + ∫ r in (-1 / 2 : ℝ)..τ,
          ∫ x in weakContL3SpatialBall,
            weakContL3MomentumFlux u Du p χ φ (x,r) := by
    calc
      _ = pairOn ⟨τ, hτ⟩ := (hpairTest ⟨τ, hτ⟩).symm
      _ = pairExt τ := by dsimp [pairExt]; rw [dite_eq_left hτ]
      _ = ell τ := (htraceEq hτ).symm
      _ = C + ∫ r in (-1 / 2 : ℝ)..τ, gFull r := hprimitiveIcc hτ
      _ = C + ∫ r in (-1 / 2 : ℝ)..τ, gFlux r := by
        rw [hIntBetween (-1 / 2) τ (by norm_num) hτ]
  have hSub (r : ℝ) : (∫ x in weakContL3SpatialBall,
      weakContL3MomentumFlux u Du p χ φ (x,r)) =
      ∫ x in vec3Ball (0 : Vec3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (x,r) i * u (x,r) j * spatialDeriv (fun y => ψ y i) j x)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          Du (x,r) i j * spatialDeriv (fun y => ψ y i) j x)
        + p (x,r) * ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x := by
    change (∫ x in vec3Ball (0 : Vec3) 1,
        weakContL3MomentumFlux u Du p χ φ (x,r)) = _
    apply setIntegral_congr_fun (isOpen_vec3Ball _ _).measurableSet
    intro x hx
    simp [weakContL3MomentumFlux, hcut, parabolicHomeomorph_symm_apply]
  calc
    _ = (C + ∫ r in (-1 / 2 : ℝ)..t.1, gFlux r) -
        (C + ∫ r in (-1 / 2 : ℝ)..s.1, gFlux r) := by
          rw [hformula t.1 htt, hformula s.1 hst]
    _ = ∫ τ in s.1..t.1, gFlux τ := by
          calc
            _ = (∫ r in (-1 / 2 : ℝ)..t.1, gFull r) -
                (∫ r in (-1 / 2 : ℝ)..s.1, gFull r) := by
                  rw [hIntBetween (-1 / 2) t.1 (by norm_num) htt,
                    hIntBetween (-1 / 2) s.1 (by norm_num) hst]
                  ring
            _ = ∫ τ in s.1..t.1, gFull τ :=
              intervalIntegral.integral_interval_sub_left
                (hgFullInt.intervalIntegrable (a := (-1 / 2 : ℝ)) (b := t.1))
                (hgFullInt.intervalIntegrable (a := (-1 / 2 : ℝ)) (b := s.1))
            _ = ∫ τ in s.1..t.1, gFlux τ := hIntBetween s.1 t.1 hst htt
    _ = ∫ τ in s.1..t.1, ∫ x in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (x,τ) i * u (x,τ) j * spatialDeriv (fun y => ψ y i) j x)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (x,τ) i j * spatialDeriv (fun y => ψ y i) j x)
          + p (x,τ) * ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x
          ∂volume := by
          congr 1
          funext τ
          change (∫ x in weakContL3SpatialBall,
            weakContL3MomentumFlux u Du p χ φ (x,τ)) = _
          exact hSub τ


/-- One measurable trace representative satisfies every smooth momentum
pairing formula on the closed time interval used in `prop:blowup-limit`. -/
theorem blowup_limit_source_pairing_formulas_with_trace
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x,t) i) (fun x => Du (x,t) i))
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    :
    ∃ v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
        Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
    ∃ W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3,
      (∀ t, ‖v t‖ ≤ (weakContL3MomentBound (u := u)).toReal) ∧
      Measurable W ∧
      (∀ t,
        (fun x => W (x,t)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
          (fun x => weakContL3OfLp (v t x))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
        ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
          (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
            (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
            (fun x => u (x,t))) ∧
      (∀ w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
        Continuous (fun t => ∫ x, inner ℝ (v t x) (w x)
          ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))) ∧
      (∀ ψ : Vec3 → Vec3,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t x i * ψ x i) -
        (∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s x i * ψ x i) =
        ∫ τ in s.1..t.1, ∫ x in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (x,τ) i * u (x,τ) j * spatialDeriv (fun y => ψ y i) j x)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (x,τ) i j * spatialDeriv (fun y => ψ y i) j x)
          + p (x,τ) * ∑ i : Fin 3, spatialDeriv (fun y => ψ y i) i x
          ∂volume) := by
  classical
  have hS3' := blowupLimit_momentum_equation_on_representative_ball hS3
  obtain ⟨v, hvbound, hvcontinuous, hvae⟩ :=
    weakContL3 hu hDu henergy hp hL3 hgrad hS3
  obtain ⟨W, hWmeas, hW⟩ :=
    weakContL3_jointlyMeasurableRepresentative v hvcontinuous
  have hWsource := blowup_limit_trace_eq_source_ae_slices v W hW hvae
  refine ⟨v, W, hvbound, hWmeas, hW, hWsource, hvcontinuous, ?_⟩
  intro ψ hψsmooth hψcompact hψsupport
  obtain ⟨χ, hχsmooth, hχcompact, hχsupport, hχrange, hχone⟩ :=
    weakContL3_cutoff_exists
  have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => weakContL3VecToLp (ψ x)) := by
    exact weakContL3VecToLp.contDiff.comp hψsmooth
  have hφsupport : tsupport (fun x => weakContL3VecToLp (ψ x)) ⊆
      tsupport ψ := by
    apply closure_minimal
    · intro x hx
      by_contra hnot
      apply hx
      have hzero : ψ x = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [hzero]
    · exact isClosed_tsupport ψ
  have hφcompact : HasCompactSupport (fun x => weakContL3VecToLp (ψ x)) := by
    apply HasCompactSupport.of_support_subset_isCompact hψcompact.isCompact
    exact (subset_tsupport _).trans hφsupport
  change HasCompactSupport (fun x => weakContL3VecToLp (ψ x)) at hφcompact
  let φ : weakContL3SmoothTest :=
    ⟨fun x => weakContL3VecToLp (ψ x), hφcompact, hφsmooth⟩
  have hcut (x : Vec3) : weakContL3CutoffTest χ φ x = ψ x := by
    by_cases hx : x ∈ vec3Ball (0 : Vec3) (3 / 4 : ℝ)
    · have hχx := hχone x hx
      rw [weakContL3CutoffTest, hχx, one_smul]
      change weakContL3OfLp (weakContL3VecToLp (ψ x)) = ψ x
      exact (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin 3 => ℝ)).apply_symm_apply (ψ x)
    · have hψzero : ψ x = 0 := by
        by_contra hne
        have : x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
        exact hx (hψsupport this)
      simp [φ, weakContL3CutoffTest, hψzero]
  let : IsFiniteMeasure (volume.restrict weakContL3SpatialBall) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hterms := weakContL3_momentumTerms_integrable
    (u := u) (Du := Du) (p := p)
    (μx := volume.restrict weakContL3SpatialBall)
    (μt := volume.restrict (Ioo (-1 : ℝ) 0))
    (by
      have hu4 := velocity_memLp_four_unit_of_essLocalData hu hDu henergy hL3 hgrad
      have hprod := localEnergy_memLp_parabolic_to_product hu4
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      simpa [weakContL3SpatialBall, parabolicHomeomorph_symm_apply] using hprod)
    (by
      have hdu2 := energyL2_components_memLp hu hDu henergy
      have hprod := localEnergy_memLp_parabolic_to_product hdu2.2
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      simpa [weakContL3SpatialBall, parabolicHomeomorph_symm_apply] using hprod)
    (by
      have hprod := localEnergy_memLp_parabolic_to_product hp
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      simpa [weakContL3SpatialBall, parabolicHomeomorph_symm_apply] using hprod)
    hχsmooth hχcompact φ
  have hweak := weakContL3_momentum_gives_productWeak
    hS3' hχsmooth hχcompact hχsupport φ
  obtain ⟨hfLoc, hgInt, hderiv⟩ :=
    weakContL3_productWeakDeriv
      (μx := volume.restrict weakContL3SpatialBall)
      (a := (-1 : ℝ)) (b := 0) hterms.1 hterms.2 hweak
  obtain ⟨ell, hellContinuous, hellAE⟩ := weakContL3_scalarTrace_exists
    (a := (-1 : ℝ)) (b := 0) (t₀ := (-1 / 2 : ℝ))
    (by norm_num) (by norm_num) hfLoc hgInt hderiv
  have hφLp32 : MemLp (fun x => weakContL3VecToLp (ψ x))
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))) :=
    hφsmooth.continuous.memLp_of_hasCompactSupport hφcompact
  let wLp : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))) :=
    hφLp32.toLp (fun x => weakContL3VecToLp (ψ x))
  have hpairCont : Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
      ∫ x, inner ℝ (v t x) (wLp x)
        ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) :=
    hvcontinuous wLp
  have hpairEqAE : ∀ᵐ t ∂volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ x, inner ℝ (v ⟨t, ht⟩ x) (wLp x)
          ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) =
        ∫ x in weakContL3SpatialBall,
          weakContL3MomentumPairing u χ φ (x,t) :=
    blowupLimit_pairing_source_slice_ae v ψ χ φ hcut hψsupport hφLp32 hvae
  have hpairTest (τ : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      (∫ x, inner ℝ (v τ x) (wLp x)
        ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) =
      ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
        ∑ i : Fin 3, v τ x i * ψ x i := by
    apply integral_congr_ae
    filter_upwards [hφLp32.coeFn_toLp] with x hx
    rw [hx]
    have hinner : inner ℝ (v τ x) (weakContL3VecToLp (ψ x)) =
        ∑ i : Fin 3, v τ x i * ψ x i := by
      simp only [weakContL3VecToLp, ContinuousLinearEquiv.coe_coe,
        PiLp.continuousLinearEquiv_symm_apply, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simpa only [weakContL3SpatialBall] using hinner
  exact blowupLimit_closed_pairing_formula χ ψ φ v wLp ell hcut hψsupport
    hpairTest hpairCont hpairEqAE ((ae_restrict_iff' measurableSet_Ioo).mpr hellAE)
    hellContinuous hgInt hfLoc hderiv

end ESS
