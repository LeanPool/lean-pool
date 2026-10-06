/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSpatial
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakFromLerayHopf
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSpaceTimeMollify
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormSerrin

/-!
# Mixed interpolation for the Leray--Hopf energy class

The finite Serrin energy equality uses the spatial interpolation between
`L²` and `L⁶`, integrated with the Leray--Hopf `L∞_t L²_x` and `L²_t H¹_x`
bounds (`lem:lps-energy-equality`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_eLpNorm_two_pow_two_eq
    {E : Type} [NormedAddCommGroup E]
    {f : Vec3 → E} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume ^ (2 : ℝ) = ∫⁻ x : Vec3, ‖f x‖ₑ ^ (2 : ℝ) := by
  have hsq (x : ℝ≥0∞) : (x ^ (1 / (2 : ℝ))) ^ (2 : ℝ) = x := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, hsq]

private theorem lps_gradient_slice_square_moment_lt_top
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du p) :
    (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ)
      ∂(volume.restrict (Ioo 0 T))) < ⊤ := by
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let G : Vec3 × ℝ → ℝ≥0∞ := fun z => ‖Du z‖ₑ ^ (2 : ℝ)
  have hGmeas : AEMeasurable G ν := (serrin_aesm_prod hU.meas_Du).enorm.pow_const _
  have hTonelli :
      (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) =
        ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖Du (x, t)‖ₑ ^ (2 : ℝ) ∂volume ∂μt := by
    rw [serrin_slab_measure_eq T]
    rw [← lintegral_prod_symm _ hGmeas]
    rfl
  have hsliceEq :
      (fun t : ℝ => eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ)) =ᵐ[μt]
        (fun t => ∫⁻ x : Vec3, ‖Du (x, t)‖ₑ ^ (2 : ℝ) ∂volume) := by
    filter_upwards [serrinWeak_slices_ae hU] with t ht
    exact lps_eLpNorm_two_pow_two_eq ht.2.1
  have htimeEq :
      (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ) ∂μt) =
        ∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ) := by
    calc
      _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖Du (x, t)‖ₑ ^ (2 : ℝ) ∂volume ∂μt :=
        lintegral_congr_ae hsliceEq
      _ = ∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ) := hTonelli.symm
  have hspaceTimeFin : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun z => le_add_self) hU.energy
  rw [htimeEq]
  exact hspaceTimeFin

/-- Almost every Leray--Hopf slice satisfies the spatial interpolation bound
between `L²` and `L⁶` at the exponent required by the finite Serrin pair
(`lem:lps-energy-equality`). -/
theorem lps_energy_class_slice_interpolation_ae
    {T s : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (hs : 3 < s) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (fun x : Vec3 => u (x, t))
          (ENNReal.ofReal (2 * s / (s - 2))) volume ≤
        3 * gagliardoNirenbergSobolevConstant ^ (3 / s) *
          (2 : ℝ≥0∞) ^ (3 / s) *
            eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ ((s - 3) / s) *
              eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (3 / s) := by
  obtain ⟨_, hU⟩ := serrinWeak_of_lerayHopf hLH
  filter_upwards [serrinWeak_slices_ae hU] with t ht
  exact lps_h1_vector_interpolation hs ht.1 ht.2.1 ht.2.2.1

/-- A Leray--Hopf field belongs to the energy-class mixed space required by
the finite Serrin energy equality (`lem:lps-energy-equality`). -/
theorem lps_energy_class_mixed_moment
    {T s : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (hs : 3 < s) :
    (∫⁻ t in Ioo 0 T,
      (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 * s / (s - 2) : ℝ)) ^
        ((2 * s / 3) / (2 * s / (s - 2)) : ℝ)) < ⊤ := by
  obtain ⟨_, hU⟩ := serrinWeak_of_lerayHopf hLH
  let alpha : ℝ := (s - 3) / s
  let gamma : ℝ := 3 / s
  let moment : ℝ := 2 * s / 3
  let q : ℝ := 2 * s / (s - 2)
  let kineticPower : ℝ := (s - 3) / 3
  let C : ℝ≥0∞ := 3 * gagliardoNirenbergSobolevConstant ^ (3 / s) *
    (2 : ℝ≥0∞) ^ (3 / s)
  let B : ℝ≥0∞ := essSup (fun t : ℝ =>
    ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo 0 T))
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hmoment : 0 < moment := by dsimp [moment]; positivity
  have hkineticPower : 0 ≤ kineticPower := by dsimp [kineticPower]; positivity
  have hαm : alpha * moment = 2 * kineticPower := by
    dsimp [alpha, moment, kineticPower]
    field_simp [ne_of_gt hs0]
  have hγm : gamma * moment = 2 := by
    dsimp [gamma, moment]
    field_simp [ne_of_gt hs0]
  have hCtop : gagliardoNirenbergSobolevConstant ≠ ⊤ :=
    (Classical.choose_spec CKN.sobolev_L6_global).1
  have hCpowTop : gagliardoNirenbergSobolevConstant ^ (3 / s : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hCtop
  have hCpow2Top : (2 : ℝ≥0∞) ^ (3 / s : ℝ) < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num)
  have hCtop' : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hCpowTop.ne)
      hCpow2Top.ne
  have hBtop : B ≠ ⊤ := hU.slice_bound.ne
  have hgradMoment := lps_gradient_slice_square_moment_lt_top hU
  have hgood : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ q) ^ (moment / q) ≤ C ^ moment * B ^ kineticPower *
            eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ) := by
    filter_upwards [lps_energy_class_slice_interpolation_ae hLH hs,
      serrinWeak_slices_ae hU,
      ae_le_essSup (f := fun t : ℝ =>
        ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ))] with t hinterp hslice hkin
    have hA2 : eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (2 : ℝ) ≤ B := by
      rw [lps_eLpNorm_two_pow_two_eq hslice.1]
      exact hkin
    have hQ :
        (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ q) ^ (moment / q) =
          eLpNorm (fun x : Vec3 => u (x, t)) (ENNReal.ofReal q) volume ^ moment := by
      have hqpos : 0 < q := by dsimp [q]; positivity
      have hqreal : (ENNReal.ofReal q).toReal = q :=
        ENNReal.toReal_ofReal hqpos.le
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_pos.mpr hqpos).ne' ENNReal.ofReal_ne_top hslice.1.aestronglyMeasurable,
        hqreal, ← ENNReal.rpow_mul]
      congr 1
      dsimp [q]
      field_simp [ne_of_gt hs0, ne_of_gt hs2]
    have hinterpC : eLpNorm (fun x : Vec3 => u (x, t))
        (ENNReal.ofReal (2 * s / (s - 2))) volume ≤
        C * eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ alpha *
          eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ gamma := by
      simpa [C] using hinterp
    have hpow := ENNReal.rpow_le_rpow hinterpC (le_of_lt hmoment)
    have hrewrite :
        (C * (eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ alpha) *
            (eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ gamma)) ^ moment =
          C ^ moment *
            (eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (alpha * moment)) *
              (eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (gamma * moment)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hmoment.le,
        ENNReal.mul_rpow_of_nonneg _ _ hmoment.le]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rw [hrewrite, hαm, hγm] at hpow
    calc
      (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ q) ^ (moment / q) =
          eLpNorm (fun x : Vec3 => u (x, t)) (ENNReal.ofReal q) volume ^ moment := hQ
      _ ≤
          C ^ moment * eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (2 * kineticPower) *
            eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ) := hpow
      _ ≤ C ^ moment * B ^ kineticPower *
            eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ) := by
        have hA : eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (2 * kineticPower) ≤
            B ^ kineticPower := by
          calc
            _ = (eLpNorm (fun x : Vec3 => u (x, t)) 2 volume ^ (2 : ℝ)) ^ kineticPower :=
              ENNReal.rpow_mul _ _ _
            _ ≤ B ^ kineticPower := ENNReal.rpow_le_rpow hA2 hkineticPower
        gcongr
  have hKtop : C ^ moment * B ^ kineticPower < ⊤ := by
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (le_of_lt hmoment) hCtop')
      (ENNReal.rpow_lt_top_of_nonneg hkineticPower hBtop)
  have hbound :
      (∫⁻ t in Ioo 0 T,
        (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ q) ^ (moment / q)) ≤
        (C ^ moment * B ^ kineticPower) *
          (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ)
            ∂(volume.restrict (Ioo 0 T))) := by
    calc
      _ ≤ ∫⁻ t : ℝ,
          C ^ moment * B ^ kineticPower *
            eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ)
              ∂(volume.restrict (Ioo 0 T)) := by
        exact lintegral_mono_ae hgood
      _ = (C ^ moment * B ^ kineticPower) *
          (∫⁻ t : ℝ, eLpNorm (fun x : Vec3 => Du (x, t)) 2 volume ^ (2 : ℝ)
            ∂(volume.restrict (Ioo 0 T))) := by
        rw [lintegral_const_mul' (C ^ moment * B ^ kineticPower) _ hKtop.ne]
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hKtop hgradMoment)

/-- The endpoint Serrin bound and the Leray--Hopf kinetic bound imply the
space-time `L⁴` membership needed by the cross-testing identity
(`lem:lps-energy-equality`). -/
theorem lps_endpoint_branch_memLp_four
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hEndpoint :
      (∫⁻ t in Ioo (0 : ℝ) T,
        (essSup (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
          (volume : Measure Vec3)) ^ (2 : ℝ)) < ⊤) :
    MemLp u (ENNReal.ofReal 4)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨_, hU⟩ := serrinWeak_of_lerayHopf hLH
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let N : ℝ → ℝ≥0∞ := fun t => essSup
    (fun x : Vec3 => ENNReal.ofReal (vec3EuclideanNorm (u (x, t)))) volume
  let K : ℝ≥0∞ := essSup (fun t : ℝ =>
    ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ)) μt
  have hKtop : K ≠ ⊤ := hU.slice_bound.ne
  have hKfinite : K < ⊤ := by simpa [K, μt] using hU.slice_bound
  have hkin := ae_le_essSup (μ := μt) (f := fun t : ℝ =>
    ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ))
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  have huProd := serrin_aesm_prod hU.meas_u
  let G : Vec3 × ℝ → ℝ≥0∞ := fun z => ‖u (z : ParabolicPoint)‖ₑ ^ (4 : ℝ)
  have hGmeas : AEMeasurable G ν :=
    huProd.enorm.pow_const _
  have hTonelli :
      (∫⁻ z in Q, ‖u z‖ₑ ^ (4 : ℝ)) =
        ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖u ((x, t) : ParabolicPoint)‖ₑ ^ (4 : ℝ) ∂volume ∂μt := by
    rw [serrin_slab_measure_eq T]
    rw [← lintegral_prod_symm _ hGmeas]
    rfl
  have hsliceBound : ∀ᵐ t ∂μt,
      ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ) ≤ K := by
    filter_upwards [hkin] with t ht
    exact ht
  have hspaceBound : ∀ t : ℝ, ∀ᵐ x ∂(volume : Measure Vec3),
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ≤ N t := by
    intro t
    exact ae_le_essSup (f := fun x : Vec3 =>
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))))
  have hsliceFourth : ∀ᵐ t ∂μt,
      (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (4 : ℝ)) ≤ K * N t ^ (2 : ℝ) := by
    filter_upwards [hsliceBound, serrinWeak_slices_ae hU] with t hK hslice
    have hspace := hspaceBound t
    have hpoint : ∀ᵐ x ∂(volume : Measure Vec3),
        ‖u (x, t)‖ₑ ^ (4 : ℝ) ≤ N t ^ (2 : ℝ) * ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
      filter_upwards [hspace] with x hx
      have hnorm : ‖u (x, t)‖ₑ ≤ ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          (CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _)
      have hle : ‖u (x, t)‖ₑ ≤ N t := hnorm.trans hx
      calc
        ‖u (x, t)‖ₑ ^ (4 : ℝ) =
            ‖u (x, t)‖ₑ ^ (2 : ℝ) * ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
          rw [show (4 : ℝ) = 2 + 2 by norm_num]
          exact ENNReal.rpow_add_of_nonneg 2 2 (by norm_num) (by norm_num)
        _ ≤ N t ^ (2 : ℝ) * ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
          exact mul_le_mul_left (ENNReal.rpow_le_rpow hle (by norm_num)) _
    calc
      _ ≤ ∫⁻ x : Vec3, N t ^ (2 : ℝ) * ‖u (x, t)‖ₑ ^ (2 : ℝ) ∂volume :=
        lintegral_mono_ae hpoint
      _ = N t ^ (2 : ℝ) *
          (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ) ∂volume) := by
        rw [lintegral_const_mul'' _
          (hslice.1.aestronglyMeasurable.enorm.pow_const _)]
      _ ≤ N t ^ (2 : ℝ) * K := by
        calc
          _ = (∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ) ∂volume) * N t ^ (2 : ℝ) :=
            mul_comm _ _
          _ ≤ K * N t ^ (2 : ℝ) := mul_le_mul_left hK _
          _ = N t ^ (2 : ℝ) * K := mul_comm _ _
      _ = K * N t ^ (2 : ℝ) := mul_comm _ _
  have hjoint : (∫⁻ z in Q, ‖u z‖ₑ ^ (4 : ℝ)) < ⊤ := by
    rw [hTonelli]
    calc
      _ ≤ ∫⁻ t : ℝ, K * N t ^ (2 : ℝ) ∂μt := lintegral_mono_ae hsliceFourth
      _ = K * (∫⁻ t : ℝ, N t ^ (2 : ℝ) ∂μt) :=
        lintegral_const_mul' _ _ hKtop
      _ < ⊤ := by
        apply ENNReal.mul_lt_top hKfinite
        simpa [N] using hEndpoint
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hLH.2.2.1]
  rw [show (ENNReal.ofReal (4 : ℝ)).toReal = 4 by norm_num]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hjoint.ne

private theorem lps_holder_ofReal {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hrecip : p⁻¹ + q⁻¹ = 1) :
    p.HolderConjugate q :=
  ⟨by simpa using hrecip, hp, hq⟩

/-- Finite Serrin control and the energy-class interpolation give the
space-time `L⁴` membership needed by the cross-testing identity
(`lem:lps-energy-equality`). -/
theorem lps_finite_branch_memLp_four
    {T s : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) (hs : 3 < s)
    (hSerrin : (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    MemLp u (ENNReal.ofReal 4)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨p, hU⟩ := serrinWeak_of_lerayHopf hLH
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod μt
  let q : ℝ := 2 * s / (s - 2)
  let ell : ℝ := 2 * s / (s - 3)
  let moment : ℝ := 2 * s / 3
  let R : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : Vec3,
    ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s
  let A : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : Vec3,
    ‖u (x, t)‖ₑ ^ s
  let B : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : Vec3,
    ‖u (x, t)‖ₑ ^ q
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hs3 : 0 < s - 3 := by linarith only [hs]
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hmpos : 0 < moment := by dsimp [moment]; positivity
  have hspatialInv : (s / 2)⁻¹ + (q / 2)⁻¹ = 1 := by
    dsimp [q]
    field_simp [ne_of_gt hs0, ne_of_gt hs2]
    ring
  have htimeInv : (ell / 2)⁻¹ + (moment / 2)⁻¹ = 1 := by
    dsimp [ell, moment]
    field_simp [ne_of_gt hs0, ne_of_gt hs3]
    ring
  have hspatialHolder : (s / 2).HolderConjugate (q / 2) :=
    lps_holder_ofReal (by positivity) (by positivity) hspatialInv
  have htimeHolder : (ell / 2).HolderConjugate (moment / 2) :=
    lps_holder_ofReal (by positivity) (by positivity) htimeInv
  have huMeas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := hU.meas_u
  have huProd := serrin_aesm_prod huMeas
  have hAmeas : AEMeasurable A μt := by
    exact (huProd.enorm.pow_const s).lintegral_prod_left'
  have hBmeas : AEMeasurable B μt := by
    exact (huProd.enorm.pow_const q).lintegral_prod_left'
  have hRfin : (∫⁻ t : ℝ, R t ^ (ell / s) ∂μt) < ⊤ := by
    simpa [R, ell, μt] using hSerrin
  have hBfin : (∫⁻ t : ℝ, B t ^ (moment / q) ∂μt) < ⊤ := by
    simpa [B, q, moment, μt] using lps_energy_class_mixed_moment hLH hs
  have hAleR : ∀ t : ℝ, A t ≤ R t := by
    intro t
    apply lintegral_mono
    intro x
    have hnorm : ‖u (x, t)‖ₑ ≤ ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        (CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm _)
    exact ENNReal.rpow_le_rpow hnorm (by positivity)
  have hfmeas : AEMeasurable (fun t : ℝ => A t ^ (2 / s)) μt :=
    (ENNReal.continuous_rpow_const (y := 2 / s)).measurable.comp_aemeasurable hAmeas
  have hGmeas : AEMeasurable (fun t : ℝ => B t ^ (2 / q)) μt :=
    (ENNReal.continuous_rpow_const (y := 2 / q)).measurable.comp_aemeasurable hBmeas
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μt htimeHolder hfmeas hGmeas
  have hfpowFin :
      (∫⁻ t : ℝ, (A t ^ (2 / s)) ^ (ell / 2) ∂μt) < ⊤ := by
    have hpoint (t : ℝ) : (A t ^ (2 / s)) ^ (ell / 2) ≤ R t ^ (ell / s) := by
      rw [← ENNReal.rpow_mul]
      have harith : (2 / s) * (ell / 2) = ell / s := by
        dsimp [ell]
        field_simp [ne_of_gt hs0, ne_of_gt hs3]
      rw [harith]
      exact ENNReal.rpow_le_rpow (hAleR t) (by positivity)
    exact lt_of_le_of_lt (lintegral_mono hpoint) hRfin
  have hgpowFin :
      (∫⁻ t : ℝ, (B t ^ (2 / q)) ^ (moment / 2) ∂μt) < ⊤ := by
    have heq : (fun t : ℝ => (B t ^ (2 / q)) ^ (moment / 2)) =
        fun t => B t ^ (moment / q) := by
      funext t
      rw [← ENNReal.rpow_mul]
      have harith : (2 / q) * (moment / 2) = moment / q := by ring
      rw [harith]
    rw [heq]
    exact hBfin
  have hHolderFin :
      (∫⁻ t : ℝ, A t ^ (2 / s) * B t ^ (2 / q) ∂μt) < ⊤ := by
    have hleft : (∫⁻ t : ℝ,
        (A t ^ (2 / s)) ^ (ell / 2) ∂μt) ^ (1 / (ell / 2)) < ⊤ := by
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hfpowFin.ne
    have hright : (∫⁻ t : ℝ,
        (B t ^ (2 / q)) ^ (moment / 2) ∂μt) ^ (1 / (moment / 2)) < ⊤ := by
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hgpowFin.ne
    exact lt_of_le_of_lt hHolder (ENNReal.mul_lt_top hleft hright)
  have hgoodSlice : ∀ᵐ t ∂μt,
      ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (4 : ℝ) ≤ A t ^ (2 / s) * B t ^ (2 / q) := by
    filter_upwards [serrinWeak_slices_ae hU] with t ht
    let wt : Vec3 → ℝ≥0∞ := fun x => ‖u (x, t)‖ₑ ^ s
    let vt : Vec3 → ℝ≥0∞ := fun x => ‖u (x, t)‖ₑ ^ q
    have hwt : AEMeasurable wt volume := ht.1.aestronglyMeasurable.enorm.pow_const s
    have hvt : AEMeasurable vt volume := ht.1.aestronglyMeasurable.enorm.pow_const q
    have hwpow : AEMeasurable (fun x => wt x ^ (2 / s)) volume :=
      (ENNReal.continuous_rpow_const (y := 2 / s)).measurable.comp_aemeasurable hwt
    have hvpow : AEMeasurable (fun x => vt x ^ (2 / q)) volume :=
      (ENNReal.continuous_rpow_const (y := 2 / q)).measurable.comp_aemeasurable hvt
    have hprod : (fun x : Vec3 =>
        wt x ^ (2 / s) * vt x ^ (2 / q)) = fun x => ‖u (x, t)‖ₑ ^ (4 : ℝ) := by
      funext x
      let v : ℝ≥0∞ := ‖u (x, t)‖ₑ
      change (v ^ s) ^ (2 / s) * (v ^ q) ^ (2 / q) = v ^ (4 : ℝ)
      have h1 : s * (2 / s) = 2 := by field_simp [ne_of_gt hs0]
      have h2 : q * (2 / q) = 2 := by field_simp [ne_of_gt hqpos]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, h1, h2]
      calc
        v ^ (2 : ℝ) * v ^ (2 : ℝ) = v ^ ((2 : ℝ) + 2) := by
          symm
          exact ENNReal.rpow_add_of_nonneg (2 : ℝ) 2 (by norm_num) (by norm_num)
        _ = v ^ (4 : ℝ) := by norm_num
    calc
      _ = ∫⁻ x : Vec3, wt x ^ (2 / s) * vt x ^ (2 / q) ∂volume := by
        rw [hprod]
      _ ≤ (∫⁻ x : Vec3, (wt x ^ (2 / s)) ^ (s / 2) ∂volume) ^ (1 / (s / 2)) *
          (∫⁻ x : Vec3, (vt x ^ (2 / q)) ^ (q / 2) ∂volume) ^ (1 / (q / 2)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume hspatialHolder hwpow hvpow
      _ = A t ^ (2 / s) * B t ^ (2 / q) := by
        have hwtInt : (∫⁻ x : Vec3, (wt x ^ (2 / s)) ^ (s / 2) ∂volume) = A t := by
          calc
            _ = ∫⁻ x : Vec3, wt x ∂volume := by
              apply lintegral_congr
              intro x
              dsimp [wt]
              rw [← ENNReal.rpow_mul]
              have he : (2 / s) * (s / 2) = 1 := by field_simp [ne_of_gt hs0]
              rw [he]
              simp
            _ = A t := rfl
        have hvtInt : (∫⁻ x : Vec3, (vt x ^ (2 / q)) ^ (q / 2) ∂volume) = B t := by
          calc
            _ = ∫⁻ x : Vec3, vt x ∂volume := by
              apply lintegral_congr
              intro x
              dsimp [vt]
              rw [← ENNReal.rpow_mul]
              have he : (2 / q) * (q / 2) = 1 := by field_simp [ne_of_gt hqpos]
              rw [he]
              simp
            _ = B t := rfl
        rw [hwtInt, hvtInt]
        congr 1
        · have hroot : 1 / (s / 2) = 2 / s := by field_simp [ne_of_gt hs0]
          rw [hroot]
        · have hroot : 1 / (q / 2) = 2 / q := by field_simp [ne_of_gt hqpos]
          rw [hroot]
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let F : Vec3 × ℝ → ℝ≥0∞ := fun z => ‖u (z : ParabolicPoint)‖ₑ ^ (4 : ℝ)
  have hFmeas : AEMeasurable F ν := huProd.enorm.pow_const _
  have hTonelli :
      (∫⁻ z in Q, ‖u z‖ₑ ^ (4 : ℝ)) =
        ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖u ((x, t) : ParabolicPoint)‖ₑ ^ (4 : ℝ) ∂volume ∂μt := by
    rw [serrin_slab_measure_eq T]
    rw [← lintegral_prod_symm _ hFmeas]
    rfl
  have hJoint : (∫⁻ z in Q, ‖u z‖ₑ ^ (4 : ℝ)) < ⊤ := by
    rw [hTonelli]
    exact lt_of_le_of_lt (lintegral_mono_ae hgoodSlice) hHolderFin
  rw [memLp_iff,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) huMeas]
  rw [show (ENNReal.ofReal (4 : ℝ)).toReal = 4 by norm_num]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJoint.ne

end ESS

end
