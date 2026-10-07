/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PvStokesClauses

/-!
# The zero-data Stokes estimate

`lem:pv-stokes` for a tensor `F ∈ L^{5/2}(Q_τ) ∩ L²(Q_τ)`, with pressure
`q = -P[F]`, from the strong `L²` and `L³` continuity of the forced heat response.
The response is `z = forcedHeat G` with `G = Fᵀ - q I`; the time slices of `z`
are continuous into `L²` and `L³` on `[0, τ]` and vanish at `t = 0`, `z` lies in
`L²(0, τ; H¹) ∩ L⁵(Q_τ) ∩ L⁴(Q_τ)` and is divergence free, `q ∈ L² ∩ L^{5/2}`,
the Stokes system holds in the sense of distributions, `∂ₜz = div (∇z + F)`
against divergence-free tests, the estimates hold with a constant independent of
`τ`, and `z` is the only square-integrable distributional solution with the same
pressure and a zero weak initial trace.

Norms of vector fields and tensors are sup norms of their entries; the constant
depends only on the dimension and the pressure-operator bounds at exponents `2`
and `5/2`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Collecting constants: `c · ((1 + 9K) N) ≤ (E B) N` for `c ≤ E` and
`1 + 9K ≤ B`. -/
theorem pvStokes_const_le {c E K B N : ℝ≥0∞} (hc : c ≤ E) (hK : 1 + 9 * K ≤ B) :
    c * ((1 + 9 * K) * N) ≤ E * B * N := by
  rw [← mul_assoc]
  gcongr

/-- `lem:pv-stokes`, from the strong continuity of the forced heat response. -/
theorem pvStokes_of_strongContinuity
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume) →
      (∀ i j, MemLp (G i j) 2 volume) →
      (∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) →
      (∀ t ∈ Icc 0 τ,
        MemLp (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ∧
        MemLp (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ∧
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
          forcedHeat G (x, s) - forcedHeat G (x, t)) 2 volume) (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
      (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 =>
          forcedHeat G (x, s) - forcedHeat G (x, t)) 3 volume) (𝓝[Icc 0 τ] t) (𝓝 0))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ F : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 2))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) →
      (∀ i j, MemLp (F i j) 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) →
      ∃ z : ParabolicPoint → Vec3, ∃ Dz : ParabolicPoint → Fin 3 → Vec3,
        -- zero initial datum and continuity into `L²` and `L³`
        (∀ x : Vec3, z (x, 0) = 0) ∧
        (∀ t ∈ Icc 0 τ, MemLp (fun x : Vec3 => z (x, t)) 2 volume ∧
          MemLp (fun x : Vec3 => z (x, t)) 3 volume) ∧
        (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 => z (x, s) - z (x, t)) 2 volume)
          (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
        (∀ t ∈ Icc 0 τ, Tendsto (fun s => eLpNorm (fun x : Vec3 => z (x, s) - z (x, t)) 3 volume)
          (𝓝[Icc 0 τ] t) (𝓝 0)) ∧
        -- `L²(0, τ; H¹)`, divergence free, `L⁵ ∩ L⁴`
        MemLp z 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        MemLp Dz 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        (∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ i : Fin 3,
          HasWeakGradientOn (Set.univ : Set Vec3) (fun x => z (x, s) i) (fun x => Dz (x, s) i)) ∧
        (∀ᵐ s ∂(volume.restrict (Ioo 0 τ)), ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
          ∫ x : Vec3, ∑ i : Fin 3, z (x, s) i * ψ.partialDeriv i x = 0) ∧
        MemLp z 5 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        MemLp z 4 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        -- the pressure `q = -P[F]`
        MemLp (pvStokesPressureSlab τ F) (ENNReal.ofReal 2)
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        MemLp (pvStokesPressureSlab τ F) (ENNReal.ofReal (5 / 2))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        -- `∂ₜz - Δz = div F - ∇q` in the sense of distributions on `Q_τ`
        (∀ φ : ParabolicPoint → Vec3,
          φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
          ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z p i *
              (-timePartial (fun y => φ y i) p -
                ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) =
            ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
              (-(∑ i : Fin 3, ∑ j : Fin 3, F i j p * spatialPartial (fun y => φ y j) i p) +
                pvStokesPressureSlab τ F p * ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p)) ∧
        -- `∂ₜz ∈ L²(0, τ; V')`: `∂ₜz = div H` against divergence-free tests, `H ∈ L²`
        (∃ H : ParabolicPoint → Fin 3 → Fin 3 → ℝ,
          MemLp H 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
          eLpNorm H 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
            ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) 2
              (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
          ∀ φ : ParabolicPoint → Vec3,
            φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
            (∀ p : ParabolicPoint, ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p = 0) →
            ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
                ∑ j : Fin 3, z p j * timePartial (fun y => φ y j) p =
              ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
                ∑ i : Fin 3, ∑ j : Fin 3, H p i j * spatialPartial (fun y => φ y j) i p) ∧
        -- the estimates
        (∀ t ∈ Icc 0 τ, eLpNorm (fun x : Vec3 => z (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm z 5 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        eLpNorm z 4 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * (eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) +
            eLpNorm (fun p => fun i j => F i j p) 2
              (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        (∀ t ∈ Icc 0 τ, eLpNorm (fun x : Vec3 => z (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm Dz 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun p => fun i j => F i j p) 2
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        -- uniqueness among square-integrable distributional solutions with zero trace
        (∀ z' : ParabolicPoint → Vec3,
          MemLp z' 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) →
          (∀ φ : ParabolicPoint → Vec3,
            φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 τ) →
            ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ), ∑ i : Fin 3, z' p i *
                (-timePartial (fun y => φ y i) p -
                  ∑ j : Fin 3, spatialSecondPartial (fun y => φ y i) j j p) =
              ∫ p in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
                (-(∑ i : Fin 3, ∑ j : Fin 3, F i j p * spatialPartial (fun y => φ y j) i p) +
                  pvStokesPressureSlab τ F p * ∑ j : Fin 3, spatialPartial (fun y => φ y j) j p)) →
          (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            ∃ c : ℝ → ℝ, ContinuousOn c (Icc 0 τ) ∧ c 0 = 0 ∧
              ∀ᵐ t ∂(volume.restrict (Ioo 0 τ)), c t = ∫ x, ∑ i : Fin 3, z' (x, t) i * ψ x i) →
          z' =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))] z) := by
  obtain ⟨CA, hCA, hA'⟩ := hA
  obtain ⟨CE, hCE, hest⟩ := forcedHeat_rough_estimates
  obtain ⟨CW, hCW, hweak⟩ := pvStokes_response_weak
  set K2 := ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound 2 (by norm_num))
  set K52 := ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound (5 / 2) (by norm_num))
  set E := ENNReal.ofReal (CA + CE + CW + 1)
  set B := (1 + 9 * K2) * (1 + 9 * K52)
  have hK (K : ℝ≥0∞) (hK : K ≠ ⊤) : 1 + 9 * K ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by norm_num) hK⟩
  have hEB : E * B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (hK _ ENNReal.ofReal_ne_top) (hK _ ENNReal.ofReal_ne_top))
  have hC : ENNReal.ofReal (E * B).toReal = E * B := ENNReal.ofReal_toReal hEB
  have hB2 : 1 + 9 * K2 ≤ B := le_mul_of_one_le_right' le_self_add
  have hB52 : 1 + 9 * K52 ≤ B := le_mul_of_one_le_left' le_self_add
  have hEA : ENNReal.ofReal CA ≤ E := ENNReal.ofReal_le_ofReal (by linarith only [hCE, hCW])
  have hEE : ENNReal.ofReal CE ≤ E := ENNReal.ofReal_le_ofReal (by linarith only [hCA, hCW])
  have hEW : ENNReal.ofReal CW ≤ E := ENNReal.ofReal_le_ofReal (by linarith only [hCA, hCE])
  have hEW1 : ENNReal.ofReal CW + 1 ≤ E := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hCW zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hCA, hCE])
  refine ⟨(E * B).toReal, ENNReal.toReal_nonneg, fun τ hτ F hF52 hF2 => ?_⟩
  rw [hC]
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have hF2' (i j : Fin 3) : MemLp (F i j) (ENNReal.ofReal 2) (volume.restrict Q) := by
    rw [e2]
    exact hF2 i j
  set G := pvStokesForce τ F with hGdef
  have hG52 (i j : Fin 3) : MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume :=
    pvStokesForce_memLp (by norm_num) hF2' hF52 i j
  have hG2 (i j : Fin 3) : MemLp (G i j) 2 volume := by
    rw [← e2]
    exact pvStokesForce_memLp (by norm_num) hF2' hF2' i j
  have hGsupp (i j : Fin 3) (z : ParabolicPoint) (hz : z ∉ Q) : G i j z = 0 :=
    pvStokesForce_eq_zero hz i j
  have hGb2 : eLpNorm (fun p => fun i j => G i j p) 2 (volume.restrict Q) ≤
      (1 + 9 * K2) * eLpNorm (fun p => fun i j => F i j p) 2 (volume.restrict Q) := by
    have h := pvStokesForce_eLpNorm_le (τ := τ) (F := F) (by norm_num : (1 : ℝ) < 2) hF2' hF2'
    rw [e2] at h
    exact h
  have hGb52 : eLpNorm (fun p => fun i j => G i j p) (ENNReal.ofReal (5 / 2)) (volume.restrict Q) ≤
      (1 + 9 * K52) * eLpNorm (fun p => fun i j => F i j p) (ENNReal.ofReal (5 / 2))
        (volume.restrict Q) :=
    pvStokesForce_eLpNorm_le (by norm_num) hF2' hF52
  obtain ⟨h5mem, h4mem, h5b, h4b, -, -, -⟩ := hest τ hτ G hG52 hG2 hGsupp
  obtain ⟨DZ, hDZmem, hDZb, hslice, hgradEq, hLapEq⟩ := hweak τ hτ G hG52 hG2 hGsupp
  obtain ⟨hevery, hc2, hc3⟩ := hA' τ hτ G hG52 hG2 hGsupp
  have hZ2 : MemLp (forcedHeat G) 2 (volume.restrict Q) :=
    forcedHeat_rough_memLp_two hτ hG52 hG2 hGsupp
  have hdiv := forcedHeat_divFree hτ hG2 hGsupp (pvStokesForce_doubleDiv hF2')
  obtain ⟨hq2, -⟩ := pvStokesPressureSlab_memLp (τ := τ) (F := F) (by norm_num : (1 : ℝ) < 2)
    (pvStokes_ext_memLp hF2') (pvStokes_ext_memLp hF2')
  obtain ⟨hq52, -⟩ := pvStokesPressureSlab_memLp (τ := τ) (F := F) (by norm_num : (1 : ℝ) < 5 / 2)
    (pvStokes_ext_memLp hF2') (pvStokes_ext_memLp hF52)
  have hGpos : ∀ i j (p : ParabolicPoint), G i j p ≠ 0 → 0 < p.2 := fun i j p hp => by
    by_contra hneg
    exact hp (hGsupp i j p fun h => hneg h.2.1)
  have hDz2 : MemLp (fun p => fun i j => DZ i j p) 2 (volume.restrict Q) :=
    memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => hDZmem i j
  have hFm : MemLp (fun p => fun i j => F i j p) 2 (volume.restrict Q) :=
    memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => hF2 i j
  have hEq := pvStokes_equation hZ2 hG2 hLapEq
  refine ⟨forcedHeat G, fun p i j => DZ i j p,
    fun x => forcedHeat_eq_zero_of_nonpos hGpos le_rfl,
    fun t ht => ⟨(hevery t ht).1, (hevery t ht).2.1⟩, hc2, hc3, hZ2, hDz2, hslice, hdiv,
    h5mem, h4mem, hq2.restrict _, hq52.restrict _, hEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the time derivative
    refine ⟨fun p i j => DZ j i p + F i j p, ?_, ?_,
      fun φ hφ hdivφ => pvStokes_timeDerivative hZ2 hDZmem hG2 hgradEq φ hφ hdivφ⟩
    · exact memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => (hDZmem j i).add (hF2 i j)
    · have hHm : AEStronglyMeasurable (fun p => fun i j => DZ j i p + F i j p)
          (volume.restrict Q) :=
        (memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j =>
          (hDZmem j i).add (hF2 i j)).aestronglyMeasurable
      have hpt : ∀ᵐ p ∂(volume.restrict Q), ‖fun i j => DZ j i p + F i j p‖ ≤
          ‖‖(fun i j => DZ i j p)‖ + ‖(fun i j => F i j p)‖‖ := by
        refine Eventually.of_forall fun p => ?_
        rw [Real.norm_of_nonneg (by positivity)]
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_le_pi_norm (fun l => DZ j l p) i).trans
            (norm_le_pi_norm (fun k l => DZ k l p) j)
        · exact (norm_le_pi_norm (fun l => F i l p) j).trans
            (norm_le_pi_norm (fun k l => F k l p) i)
      calc
        eLpNorm (fun p => fun i j => DZ j i p + F i j p) 2 (volume.restrict Q) ≤
            eLpNorm (fun p => ‖(fun i j => DZ i j p)‖ + ‖(fun i j => F i j p)‖) 2
              (volume.restrict Q) := eLpNorm_mono_ae hHm hpt
        _ ≤ eLpNorm (fun p => ‖(fun i j => DZ i j p)‖) 2 (volume.restrict Q) +
            eLpNorm (fun p => ‖(fun i j => F i j p)‖) 2 (volume.restrict Q) :=
          eLpNorm_add_le (by norm_num)
        _ = eLpNorm (fun p => fun i j => DZ i j p) 2 (volume.restrict Q) +
            eLpNorm (fun p => fun i j => F i j p) 2 (volume.restrict Q) := by
          rw [eLpNorm_norm _ hDz2.aestronglyMeasurable, eLpNorm_norm _ hFm.aestronglyMeasurable]
        _ ≤ ENNReal.ofReal CW * ((1 + 9 * K2) *
              eLpNorm (fun p => fun i j => F i j p) 2 (volume.restrict Q)) +
            (1 + 9 * K2) * eLpNorm (fun p => fun i j => F i j p) 2 (volume.restrict Q) := by
          gcongr
          · exact hDZb.trans (mul_le_mul_right hGb2 _)
          · exact le_mul_of_one_le_left' le_self_add
        _ = (ENNReal.ofReal CW + 1) * ((1 + 9 * K2) *
              eLpNorm (fun p => fun i j => F i j p) 2 (volume.restrict Q)) := by ring
        _ ≤ _ := pvStokes_const_le hEW1 hB2
  · intro t ht
    exact (hevery t ht).2.2.2.trans ((mul_le_mul_right hGb52 _).trans (pvStokes_const_le hEA hB52))
  · exact h5b.trans ((mul_le_mul_right hGb52 _).trans (pvStokes_const_le hEE hB52))
  · refine h4b.trans ((mul_le_mul_right (add_le_add hGb52 hGb2) _).trans ?_)
    rw [mul_add, mul_add]
    exact add_le_add (pvStokes_const_le hEE hB52) (pvStokes_const_le hEE hB2)
  · intro t ht
    exact (hevery t ht).2.2.1.trans ((mul_le_mul_right hGb2 _).trans (pvStokes_const_le hEA hB2))
  · exact hDZb.trans ((mul_le_mul_right hGb2 _).trans (pvStokes_const_le hEW hB2))
  · intro z' hz' hz'eq hz'tr
    exact pvStokes_unique_of_eq hτ _ hZ2 hz' hEq hz'eq
      (fun ψ hψ hψc => pvStokes_forcedHeat_trace hτ hG52 hGsupp ψ hψ hψc) hz'tr

end ESS

end
