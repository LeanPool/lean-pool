/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.RecedingEquation
public import LeanPool.CIVAxisymmetric.Analysis.DtPastHasDerivAtBridge
public import LeanPool.CIVAxisymmetric.Analysis.TimeSegmentLipschitzOfDerivBound
public import LeanPool.CIVAxisymmetric.Analysis.DifferentiateIntegralMulTestFunction

/-!
# Receding Time Pairing Wiring

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- `zoomTheta lam h rc zc u`, as a function of the full pair `(y, τ)`, is smooth on its
natural domain (where the recentred zoom point lies in the unit cylinder). -/
private theorem contDiffOn_zoomTheta_joint {lam h rc zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)
      {q : (ℝ × ℝ) × ℝ | zoomPointRec lam h rc zc q ∈ unitCylinder} := by
  have hζ : ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × ℝ => zoomPointRec lam h rc zc q) := contDiff_zoomPointRec lam h rc zc
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ) × ℝ => azimuthalVorticity u (zoomPointRec lam h rc zc q))
      {q : (ℝ × ℝ) × ℝ | zoomPointRec lam h rc zc q ∈ unitCylinder} :=
    (contDiffOn_azimuthalVorticity hu).comp hζ.contDiffOn (fun q hq => hq)
  have heq : (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q)
      = fun q : (ℝ × ℝ) × ℝ =>
        lam ^ 2 * lam ^ (2 * h) * azimuthalVorticity u (zoomPointRec lam h rc zc q) := by
    funext q; rfl
  rw [heq]
  exact hcomp.const_smul (lam ^ 2 * lam ^ (2 * h))

/-- The derivative of the second slice of a differentiable function of `(ℝ × ℝ) × ℝ` is the
second directional derivative. -/
private theorem hasDerivAt_slice_snd_joint {F : (ℝ × ℝ) × ℝ → ℝ} {q : (ℝ × ℝ) × ℝ}
    (hF : DifferentiableAt ℝ F q) :
    HasDerivAt (fun t : ℝ => F (q.1, t)) (fderiv ℝ F q ((0, 0), 1)) q.2 := by
  have hline : HasDerivAt (fun t : ℝ => (q.1, t)) (((0 : ℝ), (0 : ℝ)), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := hF.hasFDerivAt) (hf := hline) (hy := rfl)

/-- The `fderiv`-based time derivative `Gp`, valued via the basis vector `((0,0),1)`. -/
private noncomputable def zoomThetaTimeDeriv (lam h rc zc : ℝ) (u : ParabolicPoint → Vec3)
    (q : (ℝ × ℝ) × ℝ) : ℝ :=
  fderiv ℝ (fun q' : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q') q ((0, 0), 1)

/-- `zoomThetaTimeDeriv` agrees with the repository's `dtPast`, via `dtPast_eq_of_hasDerivAt`. -/
private theorem dtPast_zoomTheta_eq_zoomThetaTimeDeriv {lam h rc zc : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {q : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc q ∈ unitCylinder) :
    dtPast (fun q' : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q') q
      = zoomThetaTimeDeriv lam h rc zc u q := by
  have hopen := (isOpen_zoomPointRec_preimage lam h rc zc)
  have hdiff : DifferentiableAt ℝ (fun q' : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q') q :=
    ((contDiffOn_zoomTheta_joint hu).differentiableOn (by norm_num) q hp)
      |>.differentiableAt (hopen.mem_nhds hp)
  have hslice := hasDerivAt_slice_snd_joint hdiff
  exact dtPast_eq_of_hasDerivAt hslice

/-- `zoomThetaTimeDeriv` is continuous on the domain where the recentred zoom point lies in
the unit cylinder. -/
private theorem continuousOn_zoomThetaTimeDeriv {lam h rc zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContinuousOn (zoomThetaTimeDeriv lam h rc zc u)
      {q : (ℝ × ℝ) × ℝ | zoomPointRec lam h rc zc q ∈ unitCylinder} := by
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun q' : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q'))
      {q : (ℝ × ℝ) × ℝ | zoomPointRec lam h rc zc q ∈ unitCylinder} :=
    (contDiffOn_zoomTheta_joint hu).fderiv_of_isOpen (isOpen_zoomPointRec_preimage lam h rc zc)
      (by norm_num)
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (zoomThetaTimeDeriv lam h rc zc u)
      {q : (ℝ × ℝ) × ℝ | zoomPointRec lam h rc zc q ∈ unitCylinder} :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.continuousOn

/-- `zoomTheta`'s time slice at a fixed spatial point `y` has genuine derivative
`zoomThetaTimeDeriv (y, τ)` at `τ`, whenever the recentred zoom point lies in the unit
cylinder. -/
private theorem hasDerivAt_zoomTheta_time {lam h rc zc : ℝ} {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {y : ℝ × ℝ} {τ : ℝ} (hp : zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder) :
    HasDerivAt (fun τ' : ℝ => zoomTheta lam h rc zc u (y, τ'))
      (zoomThetaTimeDeriv lam h rc zc u (y, τ)) τ := by
  have hdiff : DifferentiableAt ℝ (fun q' : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q') (y, τ) :=
    ((contDiffOn_zoomTheta_joint hu).differentiableOn (by norm_num) (y, τ) hp)
      |>.differentiableAt ((isOpen_zoomPointRec_preimage lam h rc zc).mem_nhds hp)
  exact hasDerivAt_slice_snd_joint hdiff

/-- The product of a function continuous on an open set with a continuous function whose
support closes inside that set is continuous on the whole plane. -/
private theorem continuous_mul_of_tsupport_subset_mvt {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b : ℝ × ℝ → ℝ} (ha : ContinuousOn a U) (hb : Continuous b) (hbU : tsupport b ⊆ U) :
    Continuous fun y => a y * b y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ tsupport b
  · exact (ha.continuousAt (hU.mem_nhds (hbU hy))).mul hb.continuousAt
  · have hopen : IsOpen (tsupport b)ᶜ := (isClosed_tsupport b).isOpen_compl
    have hev : (fun y => a y * b y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- The time-pairing bound for `zoomTheta` at a fixed zoom scale, on a compact time
interval `Icc a b ⊆ (-∞,-1]`: a domination bound on `∫ (dtPast Θ)(·, τ) ψ` for `τ ∈ Icc a b`
gives, via differentiation under the integral sign and the mean value theorem, the literal
two-point pairing bound `hpair` needs. -/
theorem exists_time_pairing_bound_of_dtPast_bound_zoomTheta {h lam rc zc : ℝ}
    {u : ParabolicPoint → Vec3} (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) {a b : ℝ} (hab : a ≤ b) (_ : b ≤ -1)
    (hmem : ∀ y ∈ K, ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
      zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder)
    {C₀ B : ℝ} (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ interior K)
    (hdom : ∀ τ ∈ Icc a b,
      |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ) * ψ y|
        ≤ C₀ * B) :
    ∀ τ ∈ Icc a b, ∀ τ' ∈ Icc a b,
      |∫ y : ℝ × ℝ,
          (zoomTheta lam h rc zc u (y, τ) - zoomTheta lam h rc zc u (y, τ')) * ψ y|
        ≤ C₀ * B * |τ - τ'| := by
  set Dopen : Set ((ℝ × ℝ) × ℝ) := {q | zoomPointRec lam h rc zc q ∈ unitCylinder} with hDopen_def
  set s : Set ℝ := Ioo (a - 1 / 2) (b + 1 / 2) with hs_def
  have hUsubK : interior K ⊆ K := interior_subset
  have hsIcc : Icc (a - 1 / 2) (b + 1 / 2) = Icc (a - 1 / 2) (b + 1 / 2) := rfl
  have hsopen : IsOpen s := isOpen_Ioo
  have hscl : s ⊆ Icc (a - 1 / 2) (b + 1 / 2) := Ioo_subset_Icc_self
  -- the global bound on `zoomThetaTimeDeriv` over `K ×ˢ Icc (a - 1/2) (b + 1/2)`
  obtain ⟨M, hMnn, hMbound⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K, ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
        |zoomThetaTimeDeriv lam h rc zc u (y, τ)| ≤ M := by
    rcases (K ×ˢ Icc (a - 1 / 2) (b + 1 / 2) : Set ((ℝ × ℝ) × ℝ)).eq_empty_or_nonempty
      with hempty | hne
    · refine ⟨0, le_refl 0, fun y hy τ hτ => ?_⟩
      have hmemprod : (y, τ) ∈ K ×ˢ Icc (a - 1 / 2) (b + 1 / 2) := ⟨hy, hτ⟩
      rw [hempty] at hmemprod
      exact absurd hmemprod (by simp)
    · have hKbigcpt : IsCompact (K ×ˢ Icc (a - 1 / 2) (b + 1 / 2)) := hK.prod isCompact_Icc
      have hKbigsub : K ×ˢ Icc (a - 1 / 2) (b + 1 / 2) ⊆ Dopen := fun q hq =>
        hmem q.1 hq.1 q.2 hq.2
      have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => |zoomThetaTimeDeriv lam h rc zc u q|)
          (K ×ˢ Icc (a - 1 / 2) (b + 1 / 2)) :=
        ((continuousOn_zoomThetaTimeDeriv hu).mono hKbigsub).abs
      obtain ⟨q₀, hq₀mem, hq₀max⟩ := hKbigcpt.exists_isMaxOn hne hcont
      refine ⟨|zoomThetaTimeDeriv lam h rc zc u q₀|, abs_nonneg _, fun y hy τ hτ => ?_⟩
      have hmemprod : (y, τ) ∈ K ×ˢ Icc (a - 1 / 2) (b + 1 / 2) := ⟨hy, hτ⟩
      exact isMaxOn_iff.mp hq₀max (y, τ) hmemprod
  -- continuity of the `τ`-slice of `Θ * ψ` and of `zoomThetaTimeDeriv * ψ`, for `τ ∈ Icc
  -- (a - 1/2) (b + 1/2)`
  have hΘcont : ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
      Continuous fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ) * ψ y := by
    intro τ hτ
    have hUopen : IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
      (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)
    have hUsub : interior K ⊆ {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
      fun y hy => hmem y (hUsubK hy) τ hτ
    have hembed : Continuous (fun y : ℝ × ℝ => (y, τ)) := continuous_id.prodMk continuous_const
    have hΘcontOn : ContinuousOn (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ))
        {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
      ((contDiffOn_zoomTheta_joint hu).continuousOn).comp hembed.continuousOn (fun y hy => hy)
    exact continuous_mul_of_tsupport_subset_mvt (isOpen_interior (s := K))
      (hΘcontOn.mono hUsub) hψ.continuous hψU
  have hDcont : ∀ τ ∈ Icc (a - 1 / 2) (b + 1 / 2),
      Continuous fun y : ℝ × ℝ => zoomThetaTimeDeriv lam h rc zc u (y, τ) * ψ y := by
    intro τ hτ
    have hUopen : IsOpen {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
      (isOpen_zoomPointRec_preimage lam h rc zc).preimage (continuous_id.prodMk continuous_const)
    have hUsub : interior K ⊆ {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
      fun y hy => hmem y (hUsubK hy) τ hτ
    have hembed : Continuous (fun y : ℝ × ℝ => (y, τ)) := continuous_id.prodMk continuous_const
    have hDcontOn : ContinuousOn (fun y : ℝ × ℝ => zoomThetaTimeDeriv lam h rc zc u (y, τ))
        {y : ℝ × ℝ | zoomPointRec lam h rc zc (y, τ) ∈ unitCylinder} :=
      (continuousOn_zoomThetaTimeDeriv hu).comp hembed.continuousOn (fun y hy => hy)
    exact continuous_mul_of_tsupport_subset_mvt (isOpen_interior (s := K))
      (hDcontOn.mono hUsub) hψ.continuous hψU
  set boundf : ℝ × ℝ → ℝ := fun y => M * |ψ y| with hboundf_def
  have hbound_cont : Continuous boundf := continuous_const.mul hψ.continuous.abs
  have hbound_supp : HasCompactSupport boundf := by
    have : HasCompactSupport (fun y : ℝ × ℝ => |ψ y|) := hψc.abs
    exact this.mul_left
  have hbound_int : Integrable boundf := hbound_cont.integrable_of_hasCompactSupport hbound_supp
  -- the derivative fact at every `τ₀ ∈ Icc a b`
  have hHasDerivAt : ∀ τ₀ ∈ Icc a b,
      HasDerivAt (fun τ : ℝ => ∫ y : ℝ × ℝ, zoomTheta lam h rc zc u (y, τ) * ψ y)
        (∫ y : ℝ × ℝ,
          dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ₀) * ψ y) τ₀ := by
    intro τ₀ hτ₀
    have hτ₀s : τ₀ ∈ s := ⟨by linarith only [hτ₀.1, hab], by linarith only [hτ₀.2]⟩
    have hτ₀Icc : τ₀ ∈ Icc (a - 1 / 2) (b + 1 / 2) := hscl hτ₀s
    have hIntΘ : Integrable (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ₀) * ψ y) :=
      (hΘcont τ₀ hτ₀Icc).integrable_of_hasCompactSupport hψc.mul_left
    have hIntD : Integrable (fun y : ℝ × ℝ => zoomThetaTimeDeriv lam h rc zc u (y, τ₀) * ψ y) :=
      (hDcont τ₀ hτ₀Icc).integrable_of_hasCompactSupport hψc.mul_left
    have hFmeas : ∀ᶠ τ in 𝓝 τ₀, AEStronglyMeasurable
        (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ) * ψ y) volume := by
      filter_upwards [hsopen.mem_nhds hτ₀s] with τ hτ
      exact (hΘcont τ (hscl hτ)).aestronglyMeasurable
    have hFint : Integrable (fun y : ℝ × ℝ => zoomTheta lam h rc zc u (y, τ₀) * ψ y) volume :=
      hIntΘ
    have hF'meas : AEStronglyMeasurable
        (fun y : ℝ × ℝ => zoomThetaTimeDeriv lam h rc zc u (y, τ₀) * ψ y) volume :=
      hIntD.aestronglyMeasurable
    have hbound : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), ∀ τ ∈ s,
        |zoomThetaTimeDeriv lam h rc zc u (y, τ) * ψ y| ≤ boundf y := by
      refine Filter.Eventually.of_forall (fun y τ hτ => ?_)
      by_cases hyK : y ∈ K
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hMbound y hyK τ (hscl hτ)) (abs_nonneg _)
      · have hy0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hcontra => hyK (hUsubK (hψU hcontra)))
        rw [hy0]
        rw [hboundf_def]
        simp only [abs_zero, mul_zero]
        positivity
    have hdiff : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)), ∀ τ ∈ s,
        HasDerivAt (fun τ' : ℝ => zoomTheta lam h rc zc u (y, τ') * ψ y)
          (zoomThetaTimeDeriv lam h rc zc u (y, τ) * ψ y) τ := by
      refine Filter.Eventually.of_forall (fun y τ hτ => ?_)
      by_cases hyK : y ∈ K
      · exact (hasDerivAt_zoomTheta_time hu (hmem y hyK τ (hscl hτ))).mul_const (ψ y)
      · have hy0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hcontra => hyK (hUsubK (hψU hcontra)))
        rw [hy0]
        simpa using hasDerivAt_const τ (0 : ℝ)
    obtain ⟨-, hderiv⟩ := hasDerivAt_integral_mul_testfunction_of_dominated (hsopen.mem_nhds hτ₀s)
      hFmeas hFint hF'meas hbound hbound_int hdiff
    have heq : (fun y : ℝ × ℝ =>
        dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, τ₀) * ψ y)
        = fun y : ℝ × ℝ => zoomThetaTimeDeriv lam h rc zc u (y, τ₀) * ψ y := by
      funext y
      by_cases hyK : y ∈ K
      · rw [dtPast_zoomTheta_eq_zoomThetaTimeDeriv hu (hmem y hyK τ₀ hτ₀Icc)]
      · have hy0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hcontra => hyK (hUsubK (hψU hcontra)))
        rw [hy0, mul_zero, mul_zero]
    rw [heq]
    exact hderiv
  -- assembling the mean value theorem bound
  intro τ hτ τ' hτ'
  have hderivwithin : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun τ'' : ℝ => ∫ y : ℝ × ℝ, zoomTheta lam h rc zc u (y, τ'') * ψ y)
        (∫ y : ℝ × ℝ,
          dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, x) * ψ y)
        (Icc a b) x :=
    fun x hx => (hHasDerivAt x hx).hasDerivWithinAt
  have hboundderiv : ∀ x ∈ Ico a b,
      |∫ y : ℝ × ℝ, dtPast (fun q : (ℝ × ℝ) × ℝ => zoomTheta lam h rc zc u q) (y, x) * ψ y|
        ≤ C₀ * B :=
    fun x hx => hdom x (Ico_subset_Icc_self hx)
  have hmvt := abs_sub_le_of_hasDerivWithinAt_le_abs hab (mul_nonneg hC₀ hB) hderivwithin
    hboundderiv hτ hτ'
  have heq2 : (∫ y : ℝ × ℝ, zoomTheta lam h rc zc u (y, τ) * ψ y)
      - ∫ y : ℝ × ℝ, zoomTheta lam h rc zc u (y, τ') * ψ y
      = ∫ y : ℝ × ℝ, (zoomTheta lam h rc zc u (y, τ) - zoomTheta lam h rc zc u (y, τ')) * ψ y := by
    rw [← integral_sub]
    · congr 1; funext y; ring
    · refine (hΘcont τ ⟨?_, ?_⟩).integrable_of_hasCompactSupport hψc.mul_left
      · linarith only [hτ.1]
      · linarith only [hτ.2]
    · refine (hΘcont τ' ⟨?_, ?_⟩).integrable_of_hasCompactSupport hψc.mul_left
      · linarith only [hτ'.1]
      · linarith only [hτ'.2]
  rwa [heq2] at hmvt

end CIV
