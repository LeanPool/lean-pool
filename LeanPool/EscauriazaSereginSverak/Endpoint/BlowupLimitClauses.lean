/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssembly
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesPressure
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesExhaustion
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesGradient
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesTerminal
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesPressureLimit
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesBounds
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitClausesModulus

/-!
# The blow-up limit, clause by clause

`prop:blowup-limit` with the clauses (c)–(f) about the subsequence and its
limit stated as in the manuscript. The time slices of the rescaled sequence
are taken from the weakly continuous `L³(B_{3/4})` representative of
`lem:weak-cont-L3`, which agrees with the source velocity at almost every time
and with the zero-extended rescaled velocities on every fixed bounded past
cylinder for all sufficiently large `k`. Clauses (a) and (b) hold for the whole
sequence; clauses (c)–(f) concern one subsequence and its limit.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The slice pairings of a weakly continuous `L³` representative with smooth
tests carried by `B_{3/4}` are continuous on the whole closed time interval. -/
theorem blowupLimitClauses_trace_pairing_continuous
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t, (fun x => W (x,t)) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => weakContL3OfLp (v t x)))
    (hcont : ∀ w : Lp L2Vec3 (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
      Continuous (fun t => ∫ x, inner ℝ (v t x) (w x)
        ∂(volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))))
    (ψ : Vec3 → Vec3) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
      ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ), ∑ i : Fin 3, W (x,t) i * ψ x i) := by
  have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  set Ψ : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (ψ x)
  have hΨc : Continuous Ψ := (PiLp.continuous_toLp 2 _).comp hψ.continuous
  have hΨs : HasCompactSupport Ψ := hψc.comp_left (by simp)
  have hΨ : MemLp Ψ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))) :=
    (hΨc.memLp_of_hasCompactSupport hΨs).restrict _
  have h := hcont (hΨ.toLp Ψ)
  refine h.congr fun t => ?_
  apply integral_congr_ae
  filter_upwards [hΨ.coeFn_toLp, hW t] with x hx hWx
  rw [hx, hWx, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.inner_apply]
  rfl

/-- The blow-up limit at a point that is not good (`prop:blowup-limit`), with
all its clauses. For the whole sequence: the uniform pressure and gradient
bounds of (a), and the explicit pairing modulus and uniform `L^{10/3}` bound of
(b). For one subsequence: it converges strongly in `L³` of every
bounded past cylinder, slice by slice weakly in `L²_loc` at every negative
time, and in gradient weakly in `L²` of every bounded past cylinder including
its top face; the limit is in `L^∞((-∞,0); L³)`, it is suitable on every
bounded past cylinder with the whole-space pressure `P[u ⊗ u]`, the rescaled
pressures and their fixed split converge in `L^{3/2}`, the terminal slices
converge weakly in `L²_loc` to a slice vanishing on every unit ball which is
the weak trace of the limit from below, and the bad-point lower bound holds
for every admissible scale while the energies vanish in the limit if the limit
velocity vanishes on a past slab longer than one. -/
theorem blowupLimit_clauses
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
    (ε₀ : ℝ) (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hbad : ¬ IsGoodPoint ε₀ u p (x₀, t₀))
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3, Measurable W ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
        ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
          (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
            (vec3Ball (0 : Vec3) (3 / 4 : ℝ))] (fun x => u (x,t))) ∧
      (∀ t, MemLp (fun x => W (x,t)) 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)))) ∧
      (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
          ∫ x in vec3Ball (0 : Vec3) (3 / 4 : ℝ), ∑ i : Fin 3, W (x,t) i * ψ x i)) ∧
      (∀ R a : ℝ, 0 < R → a < 0 → ∀ᶠ k in atTop,
        blowupLimitTraceRescaling W x₀ t₀ (r k) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)] blowupVelocity x₀ t₀ (r k) u) ∧
      -- clause (a)
      (∀ R a : ℝ, 0 < R → a < 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
        IntegrableOn (fun z => |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ))
          (vec3Ball 0 R ×ˢ Ioo a 0) ∧
        IntegrableOn (fun z => spatialGradientSq (blowupVelocity x₀ t₀ (r k) u)
          (blowupGradient x₀ t₀ (r k) Du) z) (spaceTimeSet (vec3Ball 0 R) (Ioo a 0)) ∧
        (∫ z in vec3Ball 0 R ×ˢ Ioo a 0,
            |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ)) +
          (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0),
            spatialGradientSq (blowupVelocity x₀ t₀ (r k) u)
              (blowupGradient x₀ t₀ (r k) Du) z) ≤ C) ∧
      -- clause (b): the pairing modulus and the uniform `L^{10/3}` bound
      (∀ K₀ : Set Vec3, IsCompact K₀ → ∀ a : ℝ, a < 0 → ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ᶠ k in atTop,
        ∀ w : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w → tsupport w ⊆ K₀ →
        ∀ Gw Lw Dw : ℝ, 0 ≤ Gw → 0 ≤ Lw → 0 ≤ Dw →
        (∀ x i j, |spatialDeriv (fun y => w y i) j x| ≤ Gw) →
        (∀ i, eLpNorm (fun x => ∑ j : Fin 3,
          spatialDeriv (fun y => spatialDeriv (fun z => w z i) j y) j x) 2 volume ≤
            ENNReal.ofReal Lw) →
        (∀ x, |∑ i : Fin 3, spatialDeriv (fun y => w y i) i x| ≤ Dw) →
        ∀ s t, s ∈ Icc a 0 → t ∈ Icc a 0 →
          |(∫ x : Vec3, ∑ i : Fin 3,
              blowupLimitTraceRescaling W x₀ t₀ (r k) (x,t) i * w x i) -
            (∫ x : Vec3, ∑ i : Fin 3,
              blowupLimitTraceRescaling W x₀ t₀ (r k) (x,s) i * w x i)| ≤
            Cc * (|t - s| * (Lw + Gw) + |t - s| ^ (1 / 3 : ℝ) * Dw)) ∧
      (∀ R a : ℝ, 0 < R → a < 0 → ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ k in atTop,
        MemLp (blowupVelocity x₀ t₀ (r k) u) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
        eLpNorm (blowupVelocity x₀ t₀ (r k) u) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
        (q : ParabolicPoint → ℝ),
        Measurable U ∧ Measurable DU ∧ Measurable q ∧
        -- clause (c)
        (∀ R a : ℝ, 0 < R → a < 0 →
          Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r (φ k)) u z - U z) 3
            (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (𝓝 0)) ∧
        (∀ t : ℝ, t < 0 → ∀ C : Set Vec3, IsCompact C →
          MemLp (fun x => U (x,t)) 2 (volume.restrict C) ∧
          ∀ g : Vec3 → Vec3, MemLp g 2 (volume.restrict C) →
            Tendsto (fun k => ∫ x in C, ∑ i : Fin 3,
                blowupLimitTraceRescaling W x₀ t₀ (r (φ k)) (x,t) i * g x i)
              atTop (𝓝 (∫ x in C, ∑ i : Fin 3, U (x,t) i * g x i))) ∧
        (∀ R a : ℝ, 0 < R → a < 0 → ∀ i j : Fin 3,
          MemLp (fun z : Vec3 × ℝ => DU z i j) 2
            (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)) ∧
          ∀ w : Vec3 × ℝ → ℝ,
            MemLp w 2 (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)) →
            Tendsto (fun k => ∫ z in vec3Ball (0 : Vec3) R ×ˢ Ioo a 0,
                blowupGradient x₀ t₀ (r (φ k)) Du z i j * w z) atTop
              (𝓝 (∫ z in vec3Ball (0 : Vec3) R ×ˢ Ioo a 0, DU z i j * w z))) ∧
        (∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))), ∀ i : Fin 3,
          HasWeakGradientOn Set.univ (fun x : Vec3 => U (x, t) i)
            (fun x : Vec3 => DU (x, t) i)) ∧
        essSup (fun t : ℝ => eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
          (3 : ℝ≥0∞) volume) (volume.restrict (Iio (0 : ℝ))) < ⊤ ∧
        (∀ R a : ℝ, 0 < R → a < 0 →
          Tendsto (fun k => eLpNorm (fun z => blowupRieszPressure x₀ t₀ (r (φ k))
              (pressureSplitRieszPressure (pressureSplitTensor u)
                (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)) z - q z)
            (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
            atTop (𝓝 0)) ∧
        (∀ R a : ℝ, 0 < R → a < 0 →
          Tendsto (fun k => eLpNorm (blowupPressureRemainder x₀ t₀ (r (φ k)) p
              (pressureSplitRieszPressure (pressureSplitTensor u)
                (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)))
            (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
            atTop (𝓝 0)) ∧
        (∀ R a : ℝ, 0 < R → a < 0 →
          Tendsto (fun k => eLpNorm (fun z => blowupPressure x₀ t₀ (r (φ k)) p z - q z)
            (3 / 2 : ℝ≥0∞) (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)))
            atTop (𝓝 0)) ∧
        -- clause (d)
        (∀ ρ a : ℝ, 0 < ρ → a < 0 →
          IsSuitableWeakSolution (vec3Ball 0 ρ) (Ioo a 0) 3 U DU q
            (0 : ParabolicPoint → Vec3)) ∧
        (∀ᵐ t ∂(volume.restrict (Iio (0 : ℝ))),
          ∃ hUt : ∀ i j, MemLp (fun x : Vec3 => U (x, t) i * U (x, t) j)
              (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure Vec3),
            (fun x : Vec3 => q (x, t)) =ᵐ[volume]
              fun x => CKN.Leray.rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
                (fun i j => (hUt i j).toLp
                  (fun y : Vec3 => U (y, t) i * U (y, t) j)) x) ∧
        -- clause (e)
        (∃ U₀ : Vec3 → Vec3,
          (∀ C : Set Vec3, IsCompact C → MemLp U₀ 2 (volume.restrict C)) ∧
          (∀ C : Set Vec3, IsCompact C → ∀ g : Vec3 → Vec3,
            MemLp g 2 (volume.restrict C) →
            Tendsto (fun k => ∫ x in C, ∑ i : Fin 3,
                blowupLimitTraceRescaling W x₀ t₀ (r (φ k)) (x, 0) i * g x i)
              atTop (𝓝 (∫ x in C, ∑ i : Fin 3, U₀ x i * g x i))) ∧
          (∀ x : Vec3, ∫⁻ y in vec3Ball x 1, ‖U₀ y‖ₑ ^ (2 : ℝ) = 0) ∧
          (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            Tendsto (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, U (x, t) i * ψ x i)
              (𝓝[<] 0) (𝓝 (∫ x : Vec3, ∑ i : Fin 3, U₀ x i * ψ x i)))) ∧
        -- clause (f)
        (∀ k, goodPointPastCylinder x₀ t₀ (r k) ⊆ goodPointDomain →
          ENNReal.ofReal (ε₀ / 8) ≤
            goodPointEnergy (blowupVelocity x₀ t₀ (r k) u)
              (blowupPressure x₀ t₀ (r k) p) 0 0 1) ∧
        (∀ T : ℝ, 1 < T →
          U =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo (-T) 0)] 0 →
          Tendsto (fun k => goodPointEnergy (blowupVelocity x₀ t₀ (r (φ k)) u)
            (blowupPressure x₀ t₀ (r (φ k)) p) 0 0 1) atTop (𝓝 0)) := by
  obtain ⟨v, W, hvbound, hWm, hW, htrace, hcont, hformula⟩ :=
    blowup_limit_source_pairing_formulas_with_trace hu hDu henergy hpLp hL3 hgrad hS3
  set Mt : ℝ := (weakContL3MomentBound (u := u)).toReal
  have hsourceW := blowupLimitAssembly_trace_indicator_bound v W Mt hvbound hW
  obtain ⟨Dm, hDm, -, hDmEq⟩ := blowupLimitAssembly_exists_measurable_version hDu
  obtain ⟨um, hum, hu_um, -⟩ := blowupLimitAssembly_exists_measurable_version hu
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    have h := hx₀
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at h
    simpa only [Set.mem_ofPred_eq, sub_zero] using h
  have hball34 : MeasurableSet (vec3Ball (0 : Vec3) (3 / 4 : ℝ)) :=
    (isOpen_vec3Ball 0 _).measurableSet
  -- the trace representative
  have hWslice : ∀ t, MemLp (fun x => W (x,t)) 3
      (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))) := by
    intro t
    have h := (hsourceW t).1
    rw [memLp_indicator_iff_restrict hball34] at h
    exact h
  have hWcont := blowupLimitClauses_trace_pairing_continuous v W hW hcont
  have hWagree : ∀ R a : ℝ, 0 < R → a < 0 → ∀ᶠ k in atTop,
      blowupLimitTraceRescaling W x₀ t₀ (r k) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0)] blowupVelocity x₀ t₀ (r k) u := by
    intro R a _ _
    have hspaceLim : Tendsto (fun k => r k * R) atTop (𝓝 0) := by
      simpa only [zero_mul] using hr0.mul_const R
    have htimeLim : Tendsto (fun k => (r k) ^ 2 * (-a)) atTop (𝓝 0) := by
      simpa using (hr0.pow 2).mul_const (-a)
    filter_upwards [hspaceLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      htimeLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with k hsk htk
    exact blowupLimitAssembly_trace_ae_eq_blowupVelocity hum hu_um W hWm htrace
      hxnorm ht₀ (hr k) hsk htk
  refine ⟨W, hWm, htrace, hWslice, fun ψ hψ hψc => hWcont ψ hψ hψc, hWagree,
    fun R a hR ha => blowupLimitClauses_energy_pressure_bounds hu hDu hp hL2 henergy hpLp hL3
      hgrad hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha,
    fun K₀ hK₀ a ha => blowupLimitClauses_pairing_modulus hu hDu hp hL2 henergy hpLp hL3 hgrad
      hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 v W hWm hW htrace hformula Mt hsourceW Dm hDm hDmEq hum
      hu_um hK₀ ha,
    fun R a hR ha => blowupLimitClauses_tenThirds_bound hu hDu hp hL2 henergy hpLp hL3 hgrad
      hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha, ?_⟩
  -- the compactness passage
  set f : ℕ → ParabolicPoint → Vec3 := fun n => blowupLimitTraceRescaling W x₀ t₀ (r n)
  set Df : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n => blowupGradient x₀ t₀ (r n) Dm
  have hfm : ∀ n, Measurable (f n) := fun n =>
    measurable_blowupLimitTraceRescaling W hWm x₀ t₀ (r n)
  have hDfm : ∀ n, Measurable (Df n) := fun n =>
    measurable_blowupLimitAssembly_blowupGradient hDm x₀ t₀ (r n)
  have hstage := blowupLimitAssembly_trace_stages hu hDu hp hL2 henergy hpLp hL3 hgrad
    hS2 hS3 x₀ t₀ r hx₀ ht₀ hr hr0 v W hWm hW htrace hformula Dm hDm hDmEq
  obtain ⟨φ, hφ, U, hU, DU, hDU, hD1, hDslice, hD2, hD3, hD4, hD5⟩ :=
    blowupLimitClauses_exhaustion_compactness f Df hfm hDfm
      (fun C hC => blowupLimitAssembly_trace_compact_slice_bound W Mt hsourceW x₀ t₀ r hr
        C hC) hstage
  set r' : ℕ → ℝ := fun k => r (φ k)
  have hr' : ∀ k, 0 < r' k := fun k => hr (φ k)
  have hr0' : Tendsto r' atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  have hconvU : ∀ R : ℝ, 0 < R → ∀ a : ℝ, a < 0 →
      Tendsto (fun k => eLpNorm (fun z => blowupVelocity x₀ t₀ (r' k) u z - U z) 3
        (volume.restrict (vec3Ball (0 : Vec3) R ×ˢ Ioo a 0))) atTop (𝓝 0) :=
    fun R hR a ha => blowupLimitAssembly_strong_Lthree hu hDu hp hL2 henergy hpLp hL3
      hgrad hS2 hS3 x₀ t₀ r' hx₀ ht₀ hr' hr0' hum hu_um W hWm htrace U hD2 R a hR ha
  have hconvV : ∀ N : ℕ, Tendsto (fun k => eLpNorm (fun z => f (φ k) z - U z) 3
      (volume.restrict (vec3Ball (0 : Vec3) ((N : ℝ) + 1) ×ˢ
        Ioo (-((N : ℝ) + 1)) 0))) atTop (𝓝 0) := by
    intro N
    set R : ℝ := (N : ℝ) + 1
    have hR : 0 < R := by positivity
    apply (hconvU R hR (-R) (by linarith only [hR])).congr'
    have hspaceLim : Tendsto (fun k => r' k * R) atTop (𝓝 0) := by
      simpa only [zero_mul] using hr0'.mul_const R
    have htimeLim : Tendsto (fun k => (r' k) ^ 2 * (-(-R))) atTop (𝓝 0) := by
      simpa using (hr0'.pow 2).mul_const (-(-R))
    filter_upwards [hspaceLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      htimeLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with k hsk htk
    have hae := blowupLimitAssembly_trace_ae_eq_blowupVelocity hum hu_um W hWm htrace
      hxnorm ht₀ (hr' k) hsk htk
    apply eLpNorm_congr_ae
    filter_upwards [hae] with z hz
    simp only [f, r'] at hz ⊢
    rw [hz]
  have hUslice := blowupLimitAssembly_slice_Lthree_of_local_convergence U hU
    (fun k => f (φ k)) (fun k => hfm (φ k)) (ENNReal.ofReal Mt)
    (fun k t => blowupLimitAssembly_trace_slice_Lthree W Mt hsourceW x₀ t₀ (r (φ k))
      (hr _) t) hconvV
  -- the window tensors of the limit and its whole-space pressure
  have hUsliceVec : ∀ a : ℝ, ∀ᵐ t ∂volume.restrict (Ioo a 0),
      eLpNorm (fun x : Vec3 => U (x,t)) 3 volume ≤ ENNReal.ofReal Mt := by
    intro a
    have h := ae_restrict_of_ae_restrict_of_subset
      (fun t (ht : t ∈ Ioo a 0) => (ht.2 : t < 0)) hUslice
    filter_upwards [h] with t ht
    exact (blowupLimitAssemblyPressure_slice_le_norm
      (hU.comp measurable_prodMk_right).aestronglyMeasurable).trans ht
  have hwindowFin : ∀ n : ℕ,
      (volume (Ioo (-((n : ℝ) + 1)) (0 : ℝ)) * (ENNReal.ofReal Mt) ^ (3 : ℝ)) ^
        (1 / 3 : ℝ) < ⊤ := by
    intro n
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    apply (ENNReal.mul_lt_top _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)).ne
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hUwin : ∀ n : ℕ, MemLp U 3 ((volume : Measure (Vec3 × ℝ)).restrict
      ((Set.univ : Set Vec3) ×ˢ Ioo (-((n : ℝ) + 1)) 0)) := fun n =>
    memLp_iff.2 ((blowupLimitAssemblyPressure_memLp_three_of_slices hU
      (hUsliceVec _) _).trans_lt (hwindowFin n))
  have hG : ∀ n i j, MemLp (blowupLimitAssemblyPressureWindowTensor U n i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := fun n i j =>
    blowupLimitAssemblyPressure_tensor_memLp_of_restrict
      (MeasurableSet.univ.prod measurableSet_Ioo) (hUwin n) i j
  obtain ⟨-, hP1, hP2, hconvP⟩ := blowupLimitClauses_pressure_limit hu hDu hp hL2
    henergy hpLp hL3 hgrad hS2 hS3 x₀ t₀ r' hx₀ ht₀ hr' hr0' U hU (ENNReal.ofReal Mt)
    ENNReal.ofReal_lt_top hUslice hconvU hG
  set q : ParabolicPoint → ℝ := blowupLimitAssemblyPressureLimit U hG with hqdef
  refine ⟨φ, hφ, U, DU, q, hU, hDU, measurable_blowupLimitAssemblyPressureLimit U hG,
    fun R a hR ha => hconvU R hR a ha, ?_, ?_, ?_, ?_, fun R a hR ha => hP1 R hR a ha,
    fun R a hR ha => hP2 R hR a ha, fun R a hR ha => hconvP R hR a ha, ?_, ?_, ?_, ?_, ?_⟩
  · -- every negative-time slice
    intro t ht C hC
    exact hDslice t ht C hC
  · -- weak gradient convergence up to the top face
    intro R a hR ha i j
    obtain ⟨Cb, -, hCb⟩ := blowupLimitClauses_energy_pressure_bounds hu hDu hp hL2 henergy
      hpLp hL3 hgrad hS2 hS3 x₀ t₀ r' hx₀ ht₀ hr' hr0' R a hR ha
    have hbound : ∀ᶠ k in atTop,
        IntegrableOn (fun z => spatialGradientSq (fun _ => (0 : Vec3))
          (blowupGradient x₀ t₀ (r (φ k)) Du) z) (spaceTimeSet (vec3Ball 0 R) (Ioo a 0)) ∧
        (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0), spatialGradientSq (fun _ => (0 : Vec3))
          (blowupGradient x₀ t₀ (r (φ k)) Du) z) ≤ Cb := by
      filter_upwards [hCb] with k hk
      obtain ⟨hpint, hgint, hle⟩ := hk
      refine ⟨hgint, ?_⟩
      have hp0 : 0 ≤ ∫ z in vec3Ball 0 R ×ˢ Ioo a 0,
          |blowupPressure x₀ t₀ (r' k) p z| ^ (3 / 2 : ℝ) :=
        integral_nonneg fun z => by positivity
      have hle' : (∫ z in spaceTimeSet (vec3Ball 0 R) (Ioo a 0),
          spatialGradientSq (blowupVelocity x₀ t₀ (r' k) u)
            (blowupGradient x₀ t₀ (r' k) Du) z) ≤ Cb := by
        linarith only [hle, hp0]
      exact hle'
    exact blowupLimitClauses_gradient_weak_to_top hDm hDmEq hr hDU hD3 hD5 ha hbound i j
  · -- weak gradients of the limit
    exact hD4
  · -- the critical slice bound of the limit
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := Mt))
    exact essSup_le_of_ae_le _ hUslice
  · -- suitability
    intro ρ a hρ ha
    exact blowupLimitAssembly_limit_suitable hu hDu hp hL2 henergy hpLp hL3 hgrad hS2 hS3
      x₀ t₀ r' hx₀ ht₀ hr' hr0' hum hu_um W hWm htrace Mt hsourceW Dm hDmEq U DU q hD5
      hconvU hD3 hconvP ρ a hρ ha
  · -- the whole-space pressure of the limit
    exact blowupLimitClauses_pressure_slice_eq U hG
  · -- the terminal slice
    have ht₀' : t₀ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 :=
      ⟨by linarith only [ht₀.1], ht₀.2⟩
    have hterm := fun C (hC : IsCompact C) =>
      blowupLimitClauses_terminal_tendsto_zero W hWm (fun t => (hsourceW t).1) ht₀' x₀ r'
        hr' hr0' hC
    refine ⟨fun _ => 0, fun C _ => MemLp.zero, ?_, ?_, ?_⟩
    · intro C hC g hg
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero]
      exact (hterm C hC).2 g hg
    · intro x
      simp
    · -- the zero weak trace from below
      intro ψ hψ hψc
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero]
      have hzero : HasZeroDistributionalVelocityTrace U := by
        apply blowupLimitAssembly_zero_trace U (fun k => f (φ k)) hD1
        · intro ψ hψ hψc
          set w : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (ψ x)
          have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hψ
          have hwc : HasCompactSupport w := hψc.comp_left (by simp)
          have hwsupp : tsupport w ⊆ tsupport ψ := tsupport_comp_subset (by simp) ψ
          obtain ⟨ρ, hρ⟩ := (hψc : IsCompact (tsupport ψ)).exists_bound_of_continuousOn
            CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn
          obtain ⟨m, hm⟩ := exists_nat_gt ρ
          have hsub : tsupport ψ ⊆ vec3Ball (0 : Vec3) ((m : ℝ) + 1) := by
            intro x hx
            have h := hρ x hx
            rw [Real.norm_eq_abs] at h
            rw [mem_vec3Ball, sub_zero]
            linarith only [(le_abs_self _).trans h, hm]
          obtain ⟨N, -, -, hmod⟩ := hstage m
          obtain ⟨A, B, θ, hA, hB, hθ, hbound⟩ := hmod (tsupport ψ) hψc hsub (-1) 0
            (fun t ht => ⟨by
              have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
              linarith only [ht.1, this], ht.2⟩) w hw hwc hwsupp
          refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
          filter_upwards [eventually_ge_atTop N] with k hk
          exact hbound (φ k) (hk.trans (hφ.id_le k))
        · intro ψ hψ hψc
          apply blowupLimitAssembly_pairing_tendsto_zero_of_unit_balls
            (fun k x => f (φ k) (x, 0))
            (fun k => ((hfm (φ k)).comp measurable_prodMk_right).aestronglyMeasurable)
            _ ψ hψ.continuous hψc
          intro c
          have h := blowup_limit_trace_terminal_rescaling_tendsto_zero W
            (fun t => (hsourceW t).1) ⟨t₀, ht₀'⟩ x₀ c r' hr' hr0'
          apply h.congr'
          filter_upwards [] with k
          congr 1
          funext x
          simp only [f, r']
          rw [blowupLimitClauses_terminal_slice_eq W ht₀' x₀ (r (φ k)) x]
      exact (hzero ψ hψ hψc).2
  · -- the bad-point lower bound at every admissible scale
    intro k hk
    exact blowupLimitClauses_bad_point_lower_bound hx₀ ht₀ hbad (hr k) hk
  · -- the zero alternative
    intro T hT hU0
    obtain ⟨-, hind, hp₁, -, -, hp₂, -⟩ := blowupLimitAssembly_source_pressure_data hu hDu
      hp hL2 henergy hpLp hL3 hgrad hS2 hS3
    have hQ1 : goodPointPastCylinder 0 0 1 = vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0 := by
      rw [goodPointPastCylinder]
      congr 1
      norm_num
    have hQ1sub : vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0 ⊆
        (Set.univ : Set Vec3) ×ˢ Ioo (-T) 0 := fun z hz =>
      ⟨mem_univ _, by linarith only [hz.2.1, hT], hz.2.2⟩
    have hU0' : U =ᵐ[volume.restrict (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)] 0 :=
      ae_restrict_of_ae_restrict_of_subset hQ1sub hU0
    have hq0 : q =ᵐ[volume.restrict (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)] 0 :=
      ae_restrict_of_ae_restrict_of_subset hQ1sub
        (blowupLimitClauses_pressure_zero_of_velocity_zero U hG hU0)
    have hvmeas : ∀ k, AEStronglyMeasurable (blowupVelocity x₀ t₀ (r' k) u)
        (volume : Measure ParabolicPoint) := fun k =>
      blowupRescaledVelocity_aestronglyMeasurable _ hind x₀ t₀ (r' k) (hr' k)
    apply blowup_limit_zero_alternative
      (fun k => blowupVelocity x₀ t₀ (r' k) u) (fun k => blowupPressure x₀ t₀ (r' k) p)
      (fun k => (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        (hvmeas k)).restrict)
      (fun k => (blowupPressure_aestronglyMeasurable_of_split p _ hp₁ hp₂ x₀ t₀ (r' k)
        (hr' k)).restrict)
    · rw [hQ1]
      have hlim3 : Tendsto (fun k => ENNReal.ofReal (Real.sqrt 3) *
          eLpNorm (fun z => blowupVelocity x₀ t₀ (r' k) u z - U z) 3
            (volume.restrict (vec3Ball (0 : Vec3) 1 ×ˢ Ioo (-1 : ℝ) 0)))
          atTop (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt 3))
          (hconvU 1 one_pos (-1) (by norm_num)) (Or.inr ENNReal.ofReal_ne_top)
        rwa [mul_zero] at h
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim3
      · exact fun k => zero_le
      · intro k
        apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
            (hvmeas k)).restrict
        filter_upwards [hU0'] with z hz
        have hz' : U z = 0 := hz
        rw [hz', sub_zero, Real.norm_eq_abs,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
        exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
    · rw [hQ1]
      apply (hconvP 1 one_pos (-1) (by norm_num)).congr'
      filter_upwards [] with k
      apply eLpNorm_congr_ae
      filter_upwards [hq0] with z hz
      have hz' : q z = 0 := hz
      rw [hz', sub_zero]

end ESS

end
