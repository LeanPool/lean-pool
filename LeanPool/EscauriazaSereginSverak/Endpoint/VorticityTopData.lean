/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityBase

/-!
# The starting data of the vorticity estimates below an exterior point

For a solution which is suitable, bounded and of bounded gradient energy near every unit past
cylinder with exterior centre and top time in `(-2, 0)`, the velocity, its gradient, the weak
gradient identity, the divergence identity and the weak vorticity equation hold on every open
unit box below an exterior top point with top time in `(-2, 0]`; at the top time `0` the box is
exhausted by the boxes below the times `-1/(n+2)` (`lem:vorticity-top-extension`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The gradient energy on a set is controlled by the Lebesgue integral of the squared norm. -/
theorem vorticityTopData_energy {W : Set (Vec3 × ℝ)} {Du : ParabolicPoint → Fin 3 → Vec3}
    {K : ℝ} (hK : 0 ≤ K)
    (hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2 (volume.restrict W))
    (hE : (∫⁻ z in W, ‖Du z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal K) :
    ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2 ≤ 9 * K := by
  have hint : ∀ i j, Integrable (fun z : Vec3 × ℝ => Du z i j ^ 2) (volume.restrict W) :=
    fun i j => (memLp_two_iff_integrable_sq (hDu i j).aestronglyMeasurable).1 (hDu i j)
  have hsum : Integrable (fun z : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2)
      (volume.restrict W) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  have hpt : ∀ z : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2 ≤ 9 * ‖Du z‖ ^ 2 := by
    intro z
    have hij : ∀ i j, Du z i j ^ 2 ≤ ‖Du z‖ ^ 2 := by
      intro i j
      have h1 : ‖Du z i j‖ ≤ ‖Du z‖ := (norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm _ i)
      have h2 : |Du z i j| ≤ ‖Du z‖ := by rwa [Real.norm_eq_abs] at h1
      nlinarith only [h2, abs_nonneg (Du z i j), sq_abs (Du z i j)]
    calc
      ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2 ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = 9 * ‖Du z‖ ^ 2 := by
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        ring
  have hlin : ENNReal.ofReal (∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2) ≤
      ENNReal.ofReal (9 * K) := by
    rw [ofReal_integral_eq_lintegral_ofReal hsum
      (Eventually.of_forall fun z => by positivity)]
    calc
      ∫⁻ z in W, ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2) ≤
          ∫⁻ z in W, 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have : ‖Du z‖ ^ (2 : ℝ) = ‖Du z‖ ^ (2 : ℕ) := by
          exact_mod_cast Real.rpow_natCast _ 2
        rw [this]
        exact hpt z
      _ = 9 * ∫⁻ z in W, ‖Du z‖ₑ ^ (2 : ℝ) := lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 9 * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (9 * K) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlin

/-- The times `-1/(n+2)` increase to `0` inside `[-1/2, 0)`. -/
theorem vorticityTopData_times :
    (∀ n : ℕ, -(1 / 2 : ℝ) ≤ -(1 / ((n : ℝ) + 2)) ∧ -(1 / ((n : ℝ) + 2)) < 0) ∧
    Monotone (fun n : ℕ => -(1 / ((n : ℝ) + 2))) ∧
    ∀ t : ℝ, t < 0 → ∃ n : ℕ, t < -(1 / ((n : ℝ) + 2)) := by
  refine ⟨fun n => ⟨?_, ?_⟩, fun m n hmn => ?_, fun t ht => ?_⟩
  · have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
    exact neg_le_neg (one_div_le_one_div_of_le (by norm_num) h2)
  · have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    linarith only [this]
  · have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    exact neg_le_neg (one_div_le_one_div_of_le (by positivity) (by linarith only [hmn']))
  · have ht' : 0 < -t := neg_pos.2 ht
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / -t)
    have h1 : 1 < (n : ℝ) * -t := (div_lt_iff₀ ht').1 hn
    have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h2 : 1 / ((n : ℝ) + 2) < -t := (div_lt_iff₀ hpos).2 (by nlinarith only [h1, ht'])
    exact ⟨n, by linarith only [h2]⟩

/-- The data of the vorticity estimates on the unit box below an exterior top point. -/
theorem vorticityExterior_boxData {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {q : ParabolicPoint → ℝ} {R₂ M E : ℝ}
    (hfam : ∀ (x₁ : Vec3) (t₁ : ℝ), R₂ < vec3EuclideanNorm x₁ →
      t₁ ∈ Ioo (-2 : ℝ) 0 →
      ∃ (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω ∧ IsOpen I ∧
        closure (parabolicCylinder x₁ t₁ 1) ⊆ spaceTimeSet Ω I ∧
        IsSuitableWeakSolution Ω I 3 U DU q
          (0 : ParabolicPoint → Vec3) ∧
        (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₁ t₁ 1)),
          vec3EuclideanNorm (U z) ≤ M) ∧
        (∫⁻ z in parabolicCylinder x₁ t₁ 1,
          ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2))
    {x₁ : Vec3} (hx₁ : R₂ < vec3EuclideanNorm x₁) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc (-2 : ℝ) 0) :
    (∀ i, MemLp (fun z : Vec3 × ℝ => U z i) 2
      (volume.restrict (vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀))) ∧
    (∀ i j, MemLp (fun z : Vec3 × ℝ => DU z i j) 2
      (volume.restrict (vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀))) ∧
    (∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀)),
      ∀ i, |U z i| ≤ M) ∧
    ∫ z in vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, ∑ j : Fin 3, DU z i j ^ 2 ≤
      18 * E ^ 2 ∧
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀, U z i * spatialPartial ψ j z =
        -∫ z in vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀, DU z i j * ψ z) ∧
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, U z i * spatialPartial ψ i z = 0) ∧
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀,
          weakVorticity DU z i * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in vec3Ball x₁ 1 ×ˢ Ioo (t₀ - 1) t₀,
          ∑ j : Fin 3, -vorticityFlux U DU z j i * spatialPartial ψ j z) := by
  have hE9 : 9 * E ^ 2 ≤ 18 * E ^ 2 := by nlinarith only [sq_nonneg E]
  rcases ht₀.2.lt_or_eq with hlt | heq
  · obtain ⟨Ω, I, hΩ, hI, hcl, hsws, hMb, hE⟩ := hfam x₁ t₀ hx₁ ⟨ht₀.1, hlt⟩
    have hsws' : IsSuitableWeakSolution Ω I 3 U DU q (fun _ => 0) := hsws
    obtain ⟨hU, hG⟩ := vorticityBase_memLp hsws' hΩ hI hcl
    exact ⟨hU, hG, vorticityBase_bound hMb, (vorticityBase_energy hG hE).trans hE9,
      vorticityBase_weakGradient hsws' hΩ hI hcl, vorticityBase_div hsws' hcl,
      vorticityBase_heat hsws' hΩ hI hcl⟩
  subst heq
  obtain ⟨htb, htmono, htcov⟩ := vorticityTopData_times
  set tn : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 2)) with htndef
  have htn : ∀ n, tn n ∈ Ioo (-2 : ℝ) 0 := fun n =>
    ⟨by linarith only [(htb n).1], (htb n).2⟩
  have hdat := fun n => hfam x₁ (tn n) hx₁ (htn n)
  choose Ωn In hΩn hIn hcln hswsn hMn hEn using hdat
  have hswsn' : ∀ n, IsSuitableWeakSolution (Ωn n) (In n) 3 U DU q (fun _ => 0) := hswsn
  set W0 := (vec3Ball x₁ 1 ×ˢ Ioo ((0 : ℝ) - 1) 0 : Set (Vec3 × ℝ)) with hW0def
  set B : ℕ → Set (Vec3 × ℝ) := fun n => vec3Ball x₁ 1 ×ˢ Ioo (tn n - 1) (tn n) with hBdef
  set Cn : ℕ → Set (Vec3 × ℝ) := fun n => vec3Ball x₁ 1 ×ˢ Ioo ((0 : ℝ) - 1) (tn n)
    with hCdef
  have hCW : ∀ n, Cn n ⊆ W0 := fun n => by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    exact ⟨hx, ht1, ht2.trans (htb n).2⟩
  have hCB : ∀ n, Cn n ⊆ B n := fun n => by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨hx, ?_, ht2⟩
    have h1 := (htb n).2
    change tn n - 1 < t
    change (0 : ℝ) - 1 < t at ht1
    linarith only [h1, ht1]
  have hWC : W0 ⊆ ⋃ n, Cn n := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    obtain ⟨n, hn⟩ := htcov t ht2
    exact mem_iUnion.2 ⟨n, hx, ht1, hn⟩
  have hWB : W0 ⊆ ⋃ n, B n := hWC.trans (iUnion_mono hCB)
  have hmem := fun n => vorticityBase_memLp (hswsn' n) (hΩn n) (hIn n) (hcln n)
  have hWb : Bornology.IsBounded W0 :=
    vorticityBox_isBounded x₁ 1 _ (Metric.isBounded_Ioo ((0 : ℝ) - 1) 0)
  have : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict W0) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  -- measurability and the velocity bound
  have hUm : ∀ i, AEStronglyMeasurable (fun z : Vec3 × ℝ => U z i) (volume.restrict W0) :=
    fun i => ((aestronglyMeasurable_iUnion_iff (s := B)).2
      fun n => ((hmem n).1 i).aestronglyMeasurable).mono_set hWB
  have hGm : ∀ i j, AEStronglyMeasurable (fun z : Vec3 × ℝ => DU z i j) (volume.restrict W0) :=
    fun i j => ((aestronglyMeasurable_iUnion_iff (s := B)).2
      fun n => ((hmem n).2 i j).aestronglyMeasurable).mono_set hWB
  have hUb : ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict W0), ∀ i, |U z i| ≤ M :=
    ae_restrict_of_ae_restrict_of_subset hWB
      ((ae_restrict_iUnion_iff B _).2 fun n => vorticityBase_bound (hMn n))
  have hU : ∀ i, MemLp (fun z : Vec3 × ℝ => U z i) 2 (volume.restrict W0) := fun i =>
    MemLp.of_bound (hUm i) M (hUb.mono fun z hz => by rw [Real.norm_eq_abs]; exact hz i)
  -- the gradient energy
  obtain ⟨ΩA, IA, -, -, -, -, -, hEA⟩ := hfam x₁ (-1 / 4) hx₁ ⟨by norm_num, by norm_num⟩
  set A := (vec3Ball x₁ 1 ×ˢ Ioo (-1 : ℝ) (-1 / 4) : Set (Vec3 × ℝ)) with hAdef
  set V : ℕ → Set (Vec3 × ℝ) := fun n => vec3Ball x₁ 1 ×ˢ Ioo (-(1 / 2) : ℝ) (tn n)
    with hVdef
  have hAQ : A ⊆ parabolicCylinder x₁ (-1 / 4) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨hx, ?_, le_of_lt ht2⟩
    change (-1 / 4 : ℝ) - 1 ^ 2 < t
    norm_num
    linarith only [ht1]
  have hVQ : ∀ n, V n ⊆ parabolicCylinder x₁ (tn n) 1 := fun n => by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨hx, ?_, le_of_lt ht2⟩
    change tn n - 1 ^ 2 < t
    have h1 := (htb n).2
    norm_num
    linarith only [ht1, h1]
  have hWAV : W0 ⊆ A ∪ ⋃ n, V n := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    rcases lt_or_ge t (-1 / 4) with h | h
    · left
      refine ⟨hx, ?_, h⟩
      change (0 : ℝ) - 1 < t at ht1
      change (-1 : ℝ) < t
      linarith only [ht1]
    · right
      obtain ⟨n, hn⟩ := htcov t ht2
      refine mem_iUnion.2 ⟨n, hx, ?_, hn⟩
      change -(1 / 2 : ℝ) < t
      linarith only [h]
  have hVmono : Monotone V := fun m n hmn =>
    prod_mono subset_rfl (Ioo_subset_Ioo_right (htmono hmn))
  have hlin : (∫⁻ z in W0, ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (2 * E ^ 2) := by
    calc
      (∫⁻ z in W0, ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ∫⁻ z in A ∪ ⋃ n, V n, ‖DU z‖ₑ ^ (2 : ℝ) :=
        lintegral_mono_set hWAV
      _ ≤ (∫⁻ z in A, ‖DU z‖ₑ ^ (2 : ℝ)) + ∫⁻ z in ⋃ n, V n, ‖DU z‖ₑ ^ (2 : ℝ) :=
        lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (E ^ 2) + ENNReal.ofReal (E ^ 2) := by
        refine add_le_add ((lintegral_mono_set hAQ).trans hEA) ?_
        rw [setLIntegral_iUnion_of_directed _ hVmono.directed_le]
        exact iSup_le fun n => (lintegral_mono_set (hVQ n)).trans (hEn n)
      _ = ENNReal.ofReal (2 * E ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
  have hG : ∀ i j, MemLp (fun z : Vec3 × ℝ => DU z i j) 2 (volume.restrict W0) := by
    intro i j
    refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top (hGm i j)).2 ?_
    have hle : ∀ z : Vec3 × ℝ, ‖DU z i j‖ₑ ≤ ‖DU z‖ₑ := fun z => by
      rw [enorm_le_iff_norm_le]
      exact (norm_le_pi_norm (DU z i) j).trans (norm_le_pi_norm _ i)
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
    simp only [ENNReal.toReal_ofNat]
    exact lintegral_mono fun z => ENNReal.rpow_le_rpow (hle z) (by norm_num)
  -- the weak identities
  have hcpt : ∀ ψ : Vec3 × ℝ → ℝ, HasCompactSupport ψ → tsupport ψ ⊆ W0 →
      ∃ n, tsupport ψ ⊆ Cn n := fun ψ hψc hψW =>
    hψc.isCompact.elim_directed_cover Cn (fun n => vorticityBox_isOpen x₁ 1 _ _)
      (hψW.trans hWC) (Monotone.directed_le fun m n hmn =>
        prod_mono subset_rfl (Ioo_subset_Ioo_right (htmono hmn)))
  have hoff : ∀ (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ), z ∉ tsupport ψ →
      ψ z = 0 ∧ (∀ j, spatialPartial ψ j z = 0) ∧ timePartial ψ z = 0 ∧
        ∀ j, spatialSecondPartial ψ j j z = 0 := by
    intro ψ z hz
    refine ⟨image_eq_zero_of_notMem_tsupport hz, fun j => vorticity_spatialPartial_off hz j,
      ?_, fun j => CKN.spatialSecondPartial_eq_zero_off_tsupport hz j j⟩
    by_contra hne
    exact hz (CKN.tsupport_timePartial_subset ψ (subset_tsupport _ hne))
  have tr : ∀ n (ψ : Vec3 × ℝ → ℝ), tsupport ψ ⊆ Cn n → ∀ h : Vec3 × ℝ → ℝ,
      (∀ z, z ∉ tsupport ψ → h z = 0) → ∫ z in W0, h z = ∫ z in B n, h z :=
    fun n ψ hn h hz =>
      (vorticity_setIntegral_congr_of_vanish (hCW n) fun z hzC => hz z fun h' => hzC (hn h')
        ).symm.trans
      (vorticity_setIntegral_congr_of_vanish (hCB n) fun z hzC => hz z fun h' => hzC (hn h'))
  refine ⟨hU, hG, hUb, ?_, ?_, ?_, ?_⟩
  · exact (vorticityTopData_energy (by positivity) hG hlin).trans (le_of_eq (by ring))
  · intro i j ψ hψ hψc hψW
    obtain ⟨n, hn⟩ := hcpt ψ hψc hψW
    have hb := vorticityBase_weakGradient (hswsn' n) (hΩn n) (hIn n) (hcln n) i j ψ hψ hψc
      (hn.trans (hCB n))
    refine (tr n ψ hn _ fun z hz => ?_).trans (hb.trans (congrArg Neg.neg
      (tr n ψ hn _ fun z hz => ?_).symm))
    · rw [(hoff ψ z hz).2.1 j, mul_zero]
    · rw [(hoff ψ z hz).1, mul_zero]
  · intro ψ hψ hψc hψW
    obtain ⟨n, hn⟩ := hcpt ψ hψc hψW
    have hb := vorticityBase_div (hswsn' n) (hcln n) ψ hψ hψc (hn.trans (hCB n))
    refine (tr n ψ hn _ fun z hz => ?_).trans hb
    exact Finset.sum_eq_zero fun i _ => by rw [(hoff ψ z hz).2.1 i, mul_zero]
  · intro i ψ hψ hψc hψW
    obtain ⟨n, hn⟩ := hcpt ψ hψc hψW
    have hb := vorticityBase_heat (hswsn' n) (hΩn n) (hIn n) (hcln n) i ψ hψ hψc
      (hn.trans (hCB n))
    refine (tr n ψ hn _ fun z hz => ?_).trans (hb.trans (congrArg Neg.neg
      (tr n ψ hn _ fun z hz => ?_).symm))
    · obtain ⟨-, -, h3, h4⟩ := hoff ψ z hz
      rw [h3, Finset.sum_eq_zero fun j _ => h4 j]
      ring
    · exact Finset.sum_eq_zero fun j _ => by rw [(hoff ψ z hz).2.1 j, mul_zero]

end ESS
