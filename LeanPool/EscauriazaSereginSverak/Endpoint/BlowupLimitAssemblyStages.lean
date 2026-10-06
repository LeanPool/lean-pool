/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyStageEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitSourcePairingModulus
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitLocalEnergy

/-!
# The stagewise hypotheses for the blow-up sequence

For the blow-up sequence of `prop:blowup-limit`, built from the trace
representative of `lem:weak-cont-L3`, each fixed bounded past cylinder has,
from some index on, weak spatial gradients on the time slices, a uniform
local gradient energy bound (the local energy step), and a uniform pairing
modulus (the pairing-modulus step). These are the stagewise hypotheses of
`blowupLimitAssembly_exhaustion_compactness`.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weakly continuous trace, as a pointwise representative extended by
zero, has global L³ slices bounded by the trace bound. -/
theorem blowupLimitAssembly_trace_indicator_bound
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3) (M : ℝ)
    (hvbound : ∀ t, ‖v t‖ ≤ M)
    (hW : ∀ t, (fun x => W (x, t)) =ᵐ[volume.restrict
      (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => weakContL3OfLp (v t x))) :
    ∀ t, MemLp ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
        (fun x => W (x, t))) 3 volume ∧
      eLpNorm (fun x => vec3EuclideanNorm
        ((vec3Ball (0 : Vec3) (3 / 4 : ℝ)).indicator
          (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal M := by
  intro t
  let B : Set Vec3 := vec3Ball (0 : Vec3) (3 / 4 : ℝ)
  have hB : MeasurableSet B := (isOpen_vec3Ball 0 (3 / 4 : ℝ)).measurableSet
  have hlocalMem : MemLp (fun x => W (x, t)) 3 (volume.restrict B) :=
    (memLp_congr_ae (hW t)).2
      ((Lp.memLp (v t)).continuousLinearMap_comp weakContL3OfLp)
  have hf : MemLp (B.indicator (fun y => W (y,t))) 3 volume :=
    (memLp_indicator_iff_restrict hB).2 hlocalMem
  have hnormEq : (fun x => vec3EuclideanNorm (B.indicator (fun y => W (y,t)) x)) =
      B.indicator (fun x => vec3EuclideanNorm (W (x, t))) := by
    funext x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, vec3EuclideanNorm_zero]
  refine ⟨hf, ?_⟩
  change eLpNorm (fun x => vec3EuclideanNorm
    (B.indicator (fun y => W (y,t)) x)) 3 volume ≤ ENNReal.ofReal M
  rw [hnormEq, eLpNorm_indicator_eq_eLpNorm_restrict hB]
  have hpointEq : (fun x => vec3EuclideanNorm (W (x, t))) =ᵐ[volume.restrict B]
      (fun x => ‖v t x‖) := by
    filter_upwards [hW t] with x hx
    rw [hx, vec3EuclideanNorm_eq_l2]
    change ‖WithLp.toLp 2 (WithLp.ofLp (v t x))‖ = ‖v t x‖
    rw [WithLp.toLp_ofLp]
  rw [eLpNorm_congr_ae hpointEq,
    eLpNorm_norm (v t) (Lp.memLp (v t)).aestronglyMeasurable,
    ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (v t)), ← Lp.norm_def]
  exact ENNReal.ofReal_le_ofReal (hvbound t)

/-- The blow-up sequence built from the trace representative satisfies the
stagewise hypotheses of the exhaustion compactness theorem. -/
theorem blowupLimitAssembly_trace_stages
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
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
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hWmeas : Measurable W)
    (hW : ∀ t, (fun x => W (x, t)) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => weakContL3OfLp (v t x)))
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x, t)))
    (hsourceFormula : ∀ ψ : Vec3 → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t y i * ψ y i) -
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s y i * ψ y i) =
        ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume)
    (Dm : ParabolicPoint → Fin 3 → Vec3) (hDm : Measurable Dm)
    (hDmEq : goodPointDomain.indicator Dm =ᵐ[volume] goodPointDomain.indicator Du) :
    ∀ m : ℕ, ∃ N : ℕ,
      (∀ n, N ≤ n → ∀ᵐ t ∂(volume.restrict (Ioo (-((m : ℝ) + 1)) 0)),
        ∀ i : Fin 3, HasWeakGradientOn (vec3Ball (0 : Vec3) ((m : ℝ) + 1))
          (fun x => blowupLimitTraceRescaling W x₀ t₀ (r n) (x, t) i)
          (fun x => blowupGradient x₀ t₀ (r n) Dm (x, t) i)) ∧
      (∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n, N ≤ n →
        (∫⁻ t in Icc (-((m : ℝ) + 1)) 0,
          ∫⁻ x in vec3Ball (0 : Vec3) ((m : ℝ) + 1),
            ENNReal.ofReal (spatialGradientSq
              (blowupLimitTraceRescaling W x₀ t₀ (r n))
              (blowupGradient x₀ t₀ (r n) Dm) (x, t))) ≤ G) ∧
      (∀ C : Set Vec3, IsCompact C → C ⊆ vec3Ball (0 : Vec3) ((m : ℝ) + 1) →
        ∀ a b : ℝ, Icc a b ⊆ Icc (-((m : ℝ) + 1)) 0 →
        ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
          HasCompactSupport w → tsupport w ⊆ C →
        ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
          ∀ n, N ≤ n → ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
            |(∫ x : Vec3, ∑ i : Fin 3,
                blowupLimitTraceRescaling W x₀ t₀ (r n) (x, t) i * w x i) -
              (∫ x : Vec3, ∑ i : Fin 3,
                blowupLimitTraceRescaling W x₀ t₀ (r n) (x,s) i * w x i)| ≤
              A * dist t s + B * (dist t s) ^ θ) := by
  intro m
  set R : ℝ := (m : ℝ) + 1 with hRdef
  have hR : 0 < R := by positivity
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hspaceLim : Tendsto (fun k => r k * R) atTop (nhds 0) := by
    simpa only [zero_mul] using hr0.mul_const R
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * R) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const R
  have hspace : ∀ᶠ k in atTop, r k * R < 1 / 4 :=
    hspaceLim.eventually (eventually_lt_nhds (by norm_num))
  have htime : ∀ᶠ k in atTop, (r k) ^ 2 * R < 1 / 4 :=
    htimeLim.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨_, Cg, Cp, _, _, hlocal⟩ :=
    blowup_limit_local_energy_pressure_of_source_data hu hDu hp hL2 henergy
      hpLp hL3 hgrad hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 R (-R) hR (by linarith only [hR])
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hspace.and (htime.and hlocal))
  obtain ⟨N₀, hN₀⟩ := blowup_limit_pairing_modulus_from_source_data hu hDu hp hL2
    henergy hpLp hL3 hgrad hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 v W hW hsourceFormula R hR
  refine ⟨max N₁ N₀, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨hsn, htn, _⟩ := hN₁ n (le_of_max_le_left hn)
    exact blowupLimitAssembly_trace_hasWeakGradientOn hDm hDmEq hgrad W hWmeas
      htrace hxnorm ht₀ (hr n) hsn htn
  · refine ⟨ENNReal.ofReal (Cg / 2), ENNReal.ofReal_lt_top, ?_⟩
    intro n hn
    obtain ⟨hsn, htn, hint, hbound, _⟩ := hN₁ n (le_of_max_le_left hn)
    exact blowupLimitAssembly_trace_gradient_energy hDm hDmEq hxnorm ht₀ (hr n) hR
      hsn (by linarith only [htn]) _ Cg hint hbound
  · intro C hC hCsub a b hab w hw hwc hwC
    obtain ⟨A, B, θ, hA, hB, hθ, h⟩ := hN₀ C hC hCsub a b hab w hw hwc hwC
    refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
    intro n hn s t hs ht
    have hn₀ : N₀ ≤ n := le_of_max_le_right hn
    have := h (n - N₀) s t hs ht
    rw [Nat.sub_add_cancel hn₀] at this
    exact this

end ESS

end
