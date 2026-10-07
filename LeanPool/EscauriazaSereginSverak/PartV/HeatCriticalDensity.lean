/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpDensity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionMollifyBounds

/-!
# Pointwise control of the heat orbit and smooth approximation

At a fixed positive time the Gaussian kernel lies in every `L^q`, `q ≥ 1`, so
Hölder's inequality bounds the heat orbit pointwise by the `Lᵖ` norm of the
datum.  Together with smooth compactly supported approximation in `Lᵖ` this
gives the approximation step of `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- At a positive time the Gaussian kernel lies in `L^q` for every `q ≥ 1`. -/
theorem heatKernel_memLp {t : ℝ} (ht : 0 < t) {q : ℝ} (hq : 1 ≤ q) :
    MemLp (fun y : Vec3 => heatKernel y t) (ENNReal.ofReal q) volume := by
  have hint := heatKernel_integrable ht
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    simpa using lt_of_lt_of_le zero_lt_one hq
  rw [← integrable_norm_rpow_iff hint.aestronglyMeasurable hq0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith only [hq])]
  set P : ℝ := (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
  refine (hint.const_mul (P ^ (q - 1))).mono'
    (hint.aestronglyMeasurable.norm.aemeasurable.pow_const q).aestronglyMeasurable ?_
  filter_upwards [] with y
  have hK := heatKernel_nonneg y t
  have hKP : heatKernel y t ≤ P := heatKernel_le_prefactor ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.norm_eq_abs, abs_of_nonneg hK]
  have hsplit : heatKernel y t ^ q = heatKernel y t ^ (q - 1) * heatKernel y t := by
    conv_lhs => rw [show q = (q - 1) + 1 by ring]
    rw [Real.rpow_add' hK (by linarith only [hq]), Real.rpow_one]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hK hKP (by linarith only [hq])) hK

/-- Hölder's inequality for the Gaussian convolution at one point: the
integrand is integrable and the value is bounded by the kernel's `L^q` norm
times the datum's `Lᵖ` norm. -/
theorem heatConv_integrable_enorm_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {t : ℝ} (ht : 0 < t) {f : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (x : Vec3) :
    Integrable (fun y : Vec3 => heatKernel y t * f (x - y)) volume ∧
      ‖heatConv t f x‖ₑ ≤ eLpNorm (fun y : Vec3 => heatKernel y t)
        (ENNReal.ofReal q) volume * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp : 0 < p := hpq.pos
  have hqpos : 0 < q := hpq.symm.pos
  have hq1 : 1 ≤ q := hpq.symm.lt.le
  have hK := heatKernel_memLp ht hq1
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hfx : AEStronglyMeasurable (fun y => f (x - y)) volume :=
    hf.aestronglyMeasurable.comp_measurePreserving hmp
  have hfxNorm : eLpNorm (fun y => f (x - y)) (ENNReal.ofReal p) volume =
      eLpNorm f (ENNReal.ofReal p) volume :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp
  have hholder : ∫⁻ y : Vec3, ‖heatKernel y t * f (x - y)‖ₑ ≤
      eLpNorm (fun y : Vec3 => heatKernel y t) (ENNReal.ofReal q) volume *
        eLpNorm f (ENNReal.ofReal p) volume := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Vec3) hpq.symm
      (f := fun y => ‖heatKernel y t‖ₑ) (g := fun y => ‖f (x - y)‖ₑ)
      hK.aestronglyMeasurable.enorm hfx.enorm
    rw [← hfxNorm,
      eLpNorm_eq_eLpNorm' (by simpa using hqpos) ENNReal.ofReal_ne_top hK.aestronglyMeasurable,
      eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top hfx,
      eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm,
      ENNReal.toReal_ofReal hqpos.le, ENNReal.toReal_ofReal hp.le]
    refine le_trans (le_of_eq ?_) h
    apply lintegral_congr
    intro y
    simp [enorm_mul]
  have hprodMeas : AEStronglyMeasurable (fun y : Vec3 => heatKernel y t * f (x - y)) volume :=
    hK.aestronglyMeasurable.mul hfx
  have hfin : eLpNorm (fun y : Vec3 => heatKernel y t) (ENNReal.ofReal q) volume *
      eLpNorm f (ENNReal.ofReal p) volume < ∞ :=
    ENNReal.mul_lt_top hK.eLpNorm_lt_top hf.eLpNorm_lt_top
  refine ⟨⟨hprodMeas, hasFiniteIntegral_iff_enorm.2 (hholder.trans_lt hfin)⟩, ?_⟩
  rw [heatConv_eq_integral]
  exact (enorm_integral_le_lintegral_enorm _).trans hholder

/-- The Gaussian convolution is linear on `Lᵖ` data and Lipschitz for the
`Lᵖ` norm at each point of positive time. -/
theorem heatConv_sub_enorm_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {t : ℝ} (ht : 0 < t) {f g : Vec3 → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume) (x : Vec3) :
    ‖heatConv t f x - heatConv t g x‖ₑ ≤ eLpNorm (fun y : Vec3 => heatKernel y t)
      (ENNReal.ofReal q) volume * eLpNorm (f - g) (ENNReal.ofReal p) volume := by
  have hfI := (heatConv_integrable_enorm_le hpq ht hf x).1
  have hgI := (heatConv_integrable_enorm_le hpq ht hg x).1
  have hsub : heatConv t f x - heatConv t g x = heatConv t (f - g) x := by
    rw [heatConv_eq_integral, heatConv_eq_integral, heatConv_eq_integral,
      ← integral_sub hfI hgI]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [Pi.sub_apply]
    ring
  rw [hsub]
  exact (heatConv_integrable_enorm_le hpq ht (hf.sub hg) x).2

/-- A vector in Vec3 has the extended norm of one of its components. -/
theorem vec3_exists_enorm_eq_component (v : Vec3) : ∃ k : Fin 3, ‖v‖ₑ = ‖v k‖ₑ := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => ‖v i‖₊)
  exact ⟨k, by rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Pi.nnnorm_def, hk]⟩

/-- The heat orbit is Lipschitz in the datum for the `Lᵖ` norm, pointwise at
every positive time. -/
theorem heatOrbit_sub_enorm_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {b b' : Vec3 → Vec3} (hb : MemLp b (ENNReal.ofReal p) volume)
    (hb' : MemLp b' (ENNReal.ofReal p) volume) {x : Vec3} {t : ℝ} (ht : 0 < t) :
    ‖heatOrbit b (x, t) - heatOrbit b' (x, t)‖ₑ ≤
      eLpNorm (fun y : Vec3 => heatKernel y t) (ENNReal.ofReal q) volume *
        eLpNorm (b - b') (ENNReal.ofReal p) volume := by
  obtain ⟨k, hk⟩ := vec3_exists_enorm_eq_component (heatOrbit b (x, t) - heatOrbit b' (x, t))
  rw [hk]
  have hbk : MemLp (fun y => b y k) (ENNReal.ofReal p) volume := memLp_pi_iff.1 hb k
  have hbk' : MemLp (fun y => b' y k) (ENNReal.ofReal p) volume := memLp_pi_iff.1 hb' k
  have h := heatConv_sub_enorm_le hpq ht hbk hbk' x
  refine h.trans ?_
  gcongr
  refine eLpNorm_mono (hbk.sub hbk').aestronglyMeasurable fun y => ?_
  simpa [Real.norm_eq_abs] using norm_le_pi_norm ((b - b') y) k

/-- Every `Lᵖ` function, `1 ≤ p < ∞`, is an `Lᵖ` limit of smooth compactly
supported functions. -/
theorem exists_smooth_compact_tendsto_eLpNorm {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : Vec3 → ℝ} (hf : MemLp f p volume) :
    ∃ g : ℕ → Vec3 → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n) ∧ HasCompactSupport (g n)) ∧
      Tendsto (fun n => eLpNorm (g n - f) p volume) atTop (nhds 0) := by
  obtain ⟨c, hc, hclim⟩ :=
    CKN.Foundation.Euclidean.memLp_exists_compactSupportContinuous_approx hp hf
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (nhds 0) := by
    simpa only [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsmall (n : ℕ) : ∃ k : ℕ, eLpNorm (fun x => CKN.mollify (c n) (ε k) (hεpos k) x -
      c n x) p volume ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    have hlim := CKN.tendsto_eLpNorm_sub_zero_mollify hp1 hp (hc n).2.2.1 hε0 hεpos
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      simp only [ENNReal.ofReal_pos]
      positivity
    exact ((ENNReal.tendsto_nhds_zero.1 hlim) _ hpos).exists
  choose k hk using hsmall
  let g : ℕ → Vec3 → ℝ := fun n => CKN.mollify (c n) (ε (k n)) (hεpos (k n))
  refine ⟨g, ?_, ?_⟩
  · intro n
    have hloc : LocallyIntegrable (c n) volume := (hc n).2.1.locallyIntegrable
    refine ⟨CKN.mollify_contDiff (hεpos (k n)) hloc, ?_⟩
    apply HasCompactSupport.intro ((hc n).1.isCompact.cthickening (r := ε (k n)))
    intro x hx
    by_contra hne
    exact hx (CKN.support_mollify_subset (hεpos (k n)) hne)
  · have hbound (n : ℕ) : eLpNorm (g n - f) p volume ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) + eLpNorm (f - c n) p volume := by
      have hsplit : g n - f = (fun x => g n x - c n x) + (-(f - c n)) := by
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
        ring
      rw [hsplit]
      refine (eLpNorm_add_le hp1).trans ?_
      rw [eLpNorm_neg]
      gcongr
      exact hk n
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)) +
        eLpNorm (f - c n) p volume) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
        have hreal : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using ENNReal.tendsto_ofReal hreal
      simpa using h1.add hclim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound

end ESS

end
