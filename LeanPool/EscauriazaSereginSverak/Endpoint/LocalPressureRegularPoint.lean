/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalPressureSmallness
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Solution

/-!
# Local Pressure Regular Point

Local pressure estimates used in the endpoint regularity argument.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


private theorem pressureD_le_scaled_pressureD
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {r R : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I 3 u Du p
      (fun _ => (0 : Vec3))) (hr : 0 < r) (hR : 0 < R)
    (hrr : r ≤ R)
    (hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I) :
    CKN.pressureD p z r ≤ (R / r) ^ (2 : ℕ) * CKN.pressureD p z R := by
  have hQrR : parabolicCylinder z.1 z.2 r ⊆ parabolicCylinder z.1 z.2 R :=
    parabolicCylinder_mono hr.le hrr
  have hInt := CKN.lin34_integrableOn_pressure_pow_cylinder hsol hR hsub
  have hmono : (∫ w in parabolicCylinder z.1 z.2 r, |p w| ^ (3 / 2 : ℝ)) ≤
      ∫ w in parabolicCylinder z.1 z.2 R, |p w| ^ (3 / 2 : ℝ) :=
    setIntegral_mono_set hInt (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall hQrR)
  unfold CKN.pressureD
  calc
    r⁻¹ ^ (2 : ℕ) *
        (∫ w in parabolicCylinder z.1 z.2 r, |p w| ^ (3 / 2 : ℝ)) ≤
      r⁻¹ ^ (2 : ℕ) *
        (∫ w in parabolicCylinder z.1 z.2 R, |p w| ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (R / r) ^ (2 : ℕ) *
      (R⁻¹ ^ (2 : ℕ) *
        ∫ w in parabolicCylinder z.1 z.2 R, |p w| ^ (3 / 2 : ℝ)) := by
      field_simp [hr.ne', hR.ne']

private theorem closure_parabolicCylinder_subset_metric_ball
    {z : ParabolicPoint} {r δ : ℝ} (hr : 0 < r) (hrδ : r < δ) :
    closure (parabolicCylinder z.1 z.2 r) ⊆ Metric.ball z δ := by
  intro q hq
  rw [closure_parabolicCylinder hr] at hq
  rcases hq with ⟨hspace, ht⟩
  rcases ht with ⟨htlo, hthi⟩
  have htime : |q.2 - z.2| ≤ r ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [htlo, hthi]
  have htimeRoot : Real.sqrt |q.2 - z.2| ≤ r := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hr.le
    · nlinarith only [htime]
  rw [Metric.mem_ball, dist_eq_parabolicDist, parabolicDist]
  apply max_lt_iff.mpr
  constructor
  · exact hspace.trans_lt hrδ
  · exact htimeRoot.trans_lt hrδ

private theorem ae_velocity_bound_on_smaller_cylinder
    {u w : ParabolicPoint → Vec3} {Q N : Set ParabolicPoint} {B : ℝ}
    (hQN : Q ⊆ N) (hQmeas : MeasurableSet Q)
    (hrep : w =ᵐ[volume.restrict N] u)
    (hbound : ∀ q ∈ N, vec3EuclideanNorm (w q) ≤ B) :
    ∀ᵐ q ∂volume.restrict Q, vec3EuclideanNorm (u q) ≤ B := by
  have hrepQ : w =ᵐ[volume.restrict Q] u := Eventually.filter_mono
    (ae_mono (Measure.restrict_mono_set volume hQN)) hrep
  filter_upwards [hrepQ, ae_restrict_mem hQmeas] with q hq hqQ
  rw [← hq]
  exact hbound q (hQN hqQ)

private theorem pressureRegularPoint_scaled_constant_le_half
    (C : ℝ) (hC : 0 ≤ C) : C * (1 / (4 * (C + 1))) ≤ 1 / 2 := by
  have hden : 0 < 4 * (C + 1) := by positivity
  have hnum : C ≤ C + 1 := by linarith only [hC]
  calc
    C * (1 / (4 * (C + 1))) = C / (4 * (C + 1)) := by ring
    _ ≤ (C + 1) / (4 * (C + 1)) := div_le_div_of_nonneg_right hnum hden.le
    _ = 1 / 4 := by field_simp [hden.ne']
    _ ≤ 1 / 2 := by norm_num

private theorem tendsto_pressureD_of_geometric_scale
    {D : ℝ → ℝ} {κ R₀ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hR₀ : 0 < R₀)
    (hDnonneg : ∀ r, 0 < r → 0 ≤ D r)
    (hDmono : ∀ r R, 0 < r → 0 < R → r ≤ R →
      R ≤ R₀ → D r ≤ (R / r) ^ (2 : ℕ) * D R)
    (hseq : Tendsto (fun n : ℕ => D (R₀ * κ ^ n)) atTop (𝓝 0)) :
    Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => κ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hκ.le hκ1
  have hR : Tendsto (fun n : ℕ => R₀ * κ ^ n) atTop (𝓝 0) :=
    by simpa using hpow.const_mul R₀
  have hpowle : ∀ n, κ ^ n ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ]
      calc
        κ ^ n * κ ≤ 1 * 1 := mul_le_mul hn hκ1.le (by positivity) (by positivity)
        _ = 1 := one_mul _
  have hRanti : Antitone (fun n : ℕ => R₀ * κ ^ n) := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    change R₀ * κ ^ (m + k) ≤ R₀ * κ ^ m
    rw [pow_add]
    calc
      R₀ * (κ ^ m * κ ^ k) ≤ R₀ * (κ ^ m * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hpowle k) (pow_nonneg hκ.le _)) hR₀.le
      _ = R₀ * κ ^ m := by ring
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    rw [eventually_nhdsWithin_iff]
    filter_upwards [] with r hr
    exact lt_of_lt_of_le ha (hDnonneg r hr)
  · intro ε hε
    have hseqε : ∀ᶠ n : ℕ in atTop,
        D (R₀ * κ ^ n) < ε * κ ^ 2 :=
      hseq.eventually (Iio_mem_nhds (mul_pos hε (sq_pos_of_pos hκ)))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hseqε
    have hRN : 0 < R₀ * κ ^ N := mul_pos hR₀ (pow_pos hκ N)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hRN] with r hrRN hr
    have hrpos : 0 < r := by simpa only [Set.mem_Ioi] using hr
    have hex : ∃ n : ℕ, R₀ * κ ^ n < r := by
      obtain ⟨n, hn⟩ := eventually_atTop.1
        (hR.eventually (Iio_mem_nhds hrpos))
      exact ⟨n, hn n le_rfl⟩
    let n : ℕ := Nat.find hex
    have hn : R₀ * κ ^ n < r := Nat.find_spec hex
    have hnmin : ∀ m < n, ¬ R₀ * κ ^ m < r := by
      intro m hm hPm
      have hmn : n ≤ m := Nat.find_min' hex hPm
      omega
    have hn_gt : N < n := by
      by_contra hnot
      have hle : n ≤ N := Nat.not_lt.mp hnot
      have hRNn : R₀ * κ ^ N ≤ R₀ * κ ^ n := hRanti hle
      exact (not_lt_of_ge (le_of_lt hrRN)) (hRNn.trans_lt hn)
    let m : ℕ := n - 1
    have hnpos : 1 ≤ n := by omega
    have hmadd : m + 1 = n := by dsimp [m]; omega
    have hmN : N ≤ m := by dsimp [m]; omega
    have hnext : R₀ * κ ^ (m + 1) < r := by simpa only [hmadd] using hn
    have hrle : r ≤ R₀ * κ ^ m := by
      by_contra hnot
      have hPm : R₀ * κ ^ m < r := lt_of_not_ge hnot
      exact hnmin m (by dsimp [m]; omega) hPm
    have hDsmall : D (R₀ * κ ^ m) < ε * κ ^ 2 := hN m hmN
    have hratio : R₀ * κ ^ m / r ≤ κ⁻¹ := by
      have hprod : κ * (R₀ * κ ^ m) < r := by
        have hpow : R₀ * κ ^ (m + 1) = κ * (R₀ * κ ^ m) := by
          rw [pow_succ]
          ring
        calc
          κ * (R₀ * κ ^ m) = R₀ * κ ^ (m + 1) := hpow.symm
          _ < r := hnext
      have hdiv : κ * (R₀ * κ ^ m) / r < 1 := by
        apply (div_lt_iff₀ hrpos).2
        simpa using hprod
      calc
        R₀ * κ ^ m / r = κ⁻¹ * (κ * (R₀ * κ ^ m) / r) := by
          field_simp [hκ.ne']
        _ ≤ κ⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_left hdiv.le (inv_nonneg.mpr hκ.le)
        _ = κ⁻¹ := mul_one _
    have hratioSq : (R₀ * κ ^ m / r) ^ (2 : ℕ) ≤ (κ⁻¹) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hratio 2
    calc
      D r ≤ (R₀ * κ ^ m / r) ^ (2 : ℕ) * D (R₀ * κ ^ m) :=
        hDmono r (R₀ * κ ^ m) hrpos (mul_pos hR₀ (pow_pos hκ m)) hrle
          (by simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (hpowle m) hR₀.le))
      _ ≤ (κ⁻¹) ^ (2 : ℕ) * D (R₀ * κ ^ m) :=
        mul_le_mul_of_nonneg_right hratioSq (hDnonneg _ (mul_pos hR₀ (pow_pos hκ m)))
      _ < (κ⁻¹) ^ (2 : ℕ) * (ε * κ ^ 2) :=
        mul_lt_mul_of_pos_left hDsmall (by positivity)
      _ = ε := by field_simp [hκ.ne']

private theorem tendsto_normalized_velocity_cube_of_ae_bound
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {z : ParabolicPoint} {R₀ B : ℝ}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I 3 u Du p
      (fun _ => (0 : Vec3)))
    (hR₀ : 0 < R₀)
    (hsubRadius : ∀ s, 0 < s → s ≤ R₀ →
      closure (parabolicCylinder z.1 z.2 s) ⊆ spaceTimeSet Ω I)
    (hUboundR₀ : ∀ᵐ q ∂volume.restrict (parabolicCylinder z.1 z.2 R₀),
      vec3EuclideanNorm (u q) ≤ B) :
    Tendsto (fun r : ℝ => r⁻¹ ^ (2 : ℕ) *
      ∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let V : ℝ → ℝ := fun r => r⁻¹ ^ (2 : ℕ) *
    ∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm (u w) ^ (3 : ℕ)
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hVupperLim : Tendsto (fun r : ℝ => ((4 * Real.pi / 3) * B ^ 3) * r ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlim : Tendsto (fun r : ℝ => ((4 * Real.pi / 3) * B ^ 3) * r ^ 3)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((4 * Real.pi / 3) * B ^ 3) * (0 : ℝ) ^ 3)) := by
      exact (tendsto_const_nhds (x := (4 * Real.pi / 3) * B ^ 3)).mul
        (hid.pow 3)
    have hzero : ((4 * Real.pi / 3) * B ^ 3) * (0 : ℝ) ^ 3 = 0 := by norm_num
    rw [hzero] at hlim
    exact hlim
  have hVnonneg : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 ≤ V r := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [] with r hr
    exact mul_nonneg (by positivity)
      (integral_nonneg (fun _ => pow_nonneg (vec3EuclideanNorm_nonneg _) 3))
  have hVupper : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      V r ≤ (4 * Real.pi / 3) * B ^ 3 * r ^ 3 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hR₀] with r hrsmall hr
    have hrpos : 0 < r := by simpa only [Set.mem_Ioi] using hr
    have hsub := hsubRadius r hrpos (le_of_lt hrsmall)
    have hUr := Eventually.filter_mono
      (ae_mono (Measure.restrict_mono_set volume
        (parabolicCylinder_mono hrpos.le (le_of_lt hrsmall)))) hUboundR₀
    have hbound := ESS.gamma_cube_le_of_ae_bound hsol hrpos hsub hUr
    simpa only [V] using hbound.2
  have hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' hVnonneg hVupper hVupperLim
  simpa only [V] using hVlim

namespace ESS

/-- The normalized velocity and pressure mass vanishes at a regular point
of a zero force suitable weak solution. -/
theorem pressure_smallness_at_regular_point
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hsol : IsSuitableWeakSolution Ω I 3 u Du p (fun _ => (0 : Vec3)))
    {z : ParabolicPoint} (hreg : IsRegularPoint Ω I u z) :
    Tendsto (fun r : ℝ => r⁻¹ ^ (2 : ℕ) *
      ∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ) + |p w| ^ (3 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsolI := CKN.isSuitableWeakSolution_iff_integrable.mp hsol
  rcases hreg.2 with ⟨N, hNopen, hzN, hNΩI, γ, hγ, hγ1, w, hrep, hholder⟩
  rcases hholder with ⟨B, K, hB, hK, hWbound, hHolder⟩
  obtain ⟨δ, hδ, hδball⟩ :=
    Metric.mem_nhds_iff.mp (hNopen.mem_nhds hzN)
  let R₀ : ℝ := δ / 2
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hR₀δ : R₀ < δ := by dsimp [R₀]; linarith only [hδ]
  have hclosureR₀ : closure (parabolicCylinder z.1 z.2 R₀) ⊆ Metric.ball z δ :=
    closure_parabolicCylinder_subset_metric_ball hR₀ hR₀δ
  have hQ₀N : parabolicCylinder z.1 z.2 R₀ ⊆ N :=
    subset_closure.trans (hclosureR₀.trans hδball)
  have hsubR₀ : closure (parabolicCylinder z.1 z.2 R₀) ⊆ spaceTimeSet Ω I :=
    hclosureR₀.trans (hδball.trans hNΩI)
  have hQ₀meas : MeasurableSet (parabolicCylinder z.1 z.2 R₀) := by
    rw [parabolicCylinder]
    exact (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hUboundR₀ : ∀ᵐ q ∂volume.restrict (parabolicCylinder z.1 z.2 R₀),
      vec3EuclideanNorm (u q) ≤ B :=
    ae_velocity_bound_on_smaller_cylinder hQ₀N hQ₀meas hrep hWbound
  have hsubRadius {s : ℝ} (hs : 0 < s) (hsR₀ : s ≤ R₀) :
      closure (parabolicCylinder z.1 z.2 s) ⊆ spaceTimeSet Ω I := by
    exact (closure_mono (parabolicCylinder_mono hs.le hsR₀)).trans hsubR₀
  have hC : 0 ≤ CKN.lin34AbsoluteConstant :=
    le_trans (CKN.lin34PointwiseConstant_nonneg CKN.lin34CZConstant_nonneg)
      (le_max_left _ _)
  let C : ℝ := CKN.lin34AbsoluteConstant
  have hC' : 0 ≤ C := by simpa [C] using hC
  let κ : ℝ := 1 / (4 * (C + 1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκlequarter : κ ≤ 1 / 4 := by
    dsimp [κ]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (C + 1))).2
    nlinarith only [hC']
  have hκhalf : κ ≤ 1 / 2 := hκlequarter.trans (by norm_num)
  have hκ1 : κ < 1 := lt_of_le_of_lt hκlequarter (by norm_num)
  have hκcube : κ ^ 3 ≤ 1 / 2 := by
    calc
      κ ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hκ.le hκlequarter 3
      _ ≤ 1 / 2 := by norm_num
  have hCκ : C * κ ≤ 1 / 2 := by
    simpa [κ] using pressureRegularPoint_scaled_constant_le_half C hC'
  let R : ℕ → ℝ := fun n => R₀ * κ ^ n
  have hRpos (n : ℕ) : 0 < R n := by
    dsimp [R]
    exact mul_pos hR₀ (pow_pos hκ n)
  have hRpowle (n : ℕ) : κ ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [pow_succ]
      exact (mul_le_mul hn hκ1.le (by positivity) (by positivity)).trans_eq (one_mul _)
  have hRle (n : ℕ) : R n ≤ R₀ := by
    dsimp [R]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hRpowle n) hR₀.le
  have hRsucc (n : ℕ) : R (n + 1) = κ * R n := by
    dsimp [R]
    rw [pow_succ]
    ring
  have hRhalf (n : ℕ) : R (n + 1) ≤ R n / 2 := by
    rw [hRsucc n]
    exact (mul_le_mul_of_nonneg_right hκhalf (hRpos n).le).trans_eq (by ring)
  have hsubR (n : ℕ) :
      closure (parabolicCylinder z.1 z.2 (R n)) ⊆ spaceTimeSet Ω I := by
    apply (closure_mono (parabolicCylinder_mono (hRpos n).le (hRle n))).trans
    exact hsubR₀
  have hUbound (n : ℕ) : ∀ᵐ q ∂volume.restrict
      (parabolicCylinder z.1 z.2 (R n)), vec3EuclideanNorm (u q) ≤ B := by
    exact Eventually.filter_mono
      (ae_mono (Measure.restrict_mono_set volume
        (parabolicCylinder_mono (hRpos n).le (hRle n)))) hUboundR₀
  let D : ℝ → ℝ := fun s => CKN.pressureD p z s
  let d : ℕ → ℝ := fun n => D (R n)
  have hDnonneg : ∀ s, 0 < s → 0 ≤ D s := by
    intro s hs
    unfold D CKN.pressureD
    exact mul_nonneg (by positivity)
      (integral_nonneg (fun _ => by positivity))
  have hDmono : ∀ r s, 0 < r → 0 < s → r ≤ s → s ≤ R₀ →
      D r ≤ (s / r) ^ (2 : ℕ) * D s := by
    intro r s hr hs hrs hsR₀
    exact pressureD_le_scaled_pressureD hsolI hr hs hrs (hsubRadius hs hsR₀)
  have hdnonneg : ∀ n, 0 ≤ d n := by
    intro n
    exact hDnonneg (R n) (hRpos n)
  have hzeroDiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun w => ∑ i : Fin 3,
        (fun _ : ParabolicPoint => (0 : Vec3)) w i * spatialPartial ψ i w)
          (tsupport ψ) volume ∧
        ∫ w in spaceTimeSet Ω I,
          ∑ i : Fin 3,
            (fun _ : ParabolicPoint => (0 : Vec3)) w i * spatialPartial ψ i w = 0 := by
    intro ψ hψ
    constructor
    · simp
    · simp
  let Kchat : ℝ := 8 * ((4 * Real.pi / 3) * B ^ 3)
  have hKchat : 0 ≤ Kchat := by dsimp [Kchat]; positivity
  let A₀ : ℝ := C * (κ⁻¹) ^ 2 * Kchat * R₀ ^ 3
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  let A : ℝ := 2 * A₀
  have hrec : ∀ n, d (n + 1) ≤ (1 / 2 : ℝ) * d n +
      A * (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    have hlin := CKN.Pressure.pressure_lin34_of_sws 3 hsolI
      (z := z) (ρ := R n) (r := R (n + 1)) (hRpos n) (hRpos (n + 1))
      (hRhalf n) (hsubR n)
    have hDstep := (hlin.1 hzeroDiv).2
    have hratio : R (n + 1) / R n = κ := by
      rw [hRsucc n]
      field_simp [ne_of_gt (hRpos n)]
    have hratioInv : (R n / R (n + 1)) ^ (2 : ℕ) = (κ⁻¹) ^ 2 := by
      rw [hRsucc n]
      field_simp [ne_of_gt (hRpos n), hκ.ne']
    rw [hratio, hratioInv] at hDstep
    have hDstep' : d (n + 1) ≤ C * ((κ⁻¹) ^ 2 *
        CKN.pressureChat u z (R n) + κ * d n) := by
      simpa [C, d, D] using hDstep
    have hchat := pressureChat_le_cubic_of_ae_bound hsolI (hRpos n)
      (hsubR n) (hUbound n)
    have hchat' : CKN.pressureChat u z (R n) ≤ Kchat * (R n) ^ 3 := by
      simpa [Kchat] using hchat
    have hpowid : (R n) ^ 3 = R₀ ^ 3 * (κ ^ 3) ^ n := by
      dsimp [R]
      rw [mul_pow]
      rw [show (κ ^ n) ^ 3 = (κ ^ 3) ^ n by
        calc
          (κ ^ n) ^ 3 = κ ^ (n * 3) := by rw [pow_mul]
          _ = κ ^ (3 * n) := by rw [Nat.mul_comm]
          _ = (κ ^ 3) ^ n := by rw [← pow_mul]]
    have hsource : C * ((κ⁻¹) ^ 2 * CKN.pressureChat u z (R n)) ≤
        A₀ * (κ ^ 3) ^ n := by
      calc
        _ ≤ C * ((κ⁻¹) ^ 2 * (Kchat * (R n) ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hchat' (by positivity)) hC'
        _ = A₀ * (κ ^ 3) ^ n := by
          dsimp [A₀]
          rw [hpowid]
          ring
    have hsourcePow : A₀ * (κ ^ 3) ^ n ≤ A * (1 / 2 : ℝ) ^ (n + 1) := by
      calc
        A₀ * (κ ^ 3) ^ n ≤ A₀ * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hκcube n) hA₀
        _ = A * (1 / 2 : ℝ) ^ (n + 1) := by
          dsimp [A]
          rw [pow_succ]
          ring
    have htermD : C * (κ * d n) ≤ (1 / 2 : ℝ) * d n := by
      calc
        C * (κ * d n) = (C * κ) * d n := by ring
        _ ≤ (1 / 2 : ℝ) * d n := mul_le_mul_of_nonneg_right hCκ (hdnonneg n)
    calc
      d (n + 1) ≤ C * ((κ⁻¹) ^ 2 * CKN.pressureChat u z (R n) + κ * d n) := hDstep'
      _ ≤ A₀ * (κ ^ 3) ^ n + (1 / 2 : ℝ) * d n := by
        simpa only [mul_add] using add_le_add hsource htermD
      _ ≤ A * (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) * d n :=
        add_le_add hsourcePow le_rfl
      _ = (1 / 2 : ℝ) * d n + A * (1 / 2 : ℝ) ^ (n + 1) := by ring
  have hdlim : Tendsto d atTop (𝓝 0) :=
    ESS.tendsto_of_half_recurrence hdnonneg hrec
  have hDlim : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_pressureD_of_geometric_scale hκ hκ1 hR₀ hDnonneg hDmono
    simpa [D, d, R] using hdlim
  let V : ℝ → ℝ := fun r => r⁻¹ ^ (2 : ℕ) *
    ∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm (u w) ^ (3 : ℕ)
  have hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [V] using tendsto_normalized_velocity_cube_of_ae_bound
      hsolI hR₀ (fun s hs hsR₀ => hsubRadius hs hsR₀) hUboundR₀
  have hsumEq : (fun r : ℝ => r⁻¹ ^ (2 : ℕ) *
      ∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ) + |p w| ^ (3 / 2 : ℝ)) =ᶠ[
      𝓝[>] (0 : ℝ)] (fun r => V r + D r) := by
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < R₀ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds hR₀] with r hr
      intro _
      exact hr
    filter_upwards [hsmall, self_mem_nhdsWithin] with r hrsmall hrmem
    have hr : 0 < r := by simpa only [Set.mem_Ioi] using hrmem
    have hrpos : 0 < r := by simpa only [Set.mem_Ioi] using hr
    have hsub := hsubRadius hrpos (le_of_lt hrsmall)
    have hvelInt := CKN.tsai_integrable_velocity_cube_on_cylinder hsolI hrpos hsub
    have hpInt := CKN.lin34_integrableOn_pressure_pow_cylinder hsolI hrpos hsub
    simp only [V, D]
    rw [integral_add hvelInt hpInt]
    unfold CKN.pressureD
    ring
  simpa only [add_zero] using (hVlim.add hDlim).congr' hsumEq.symm

end ESS
