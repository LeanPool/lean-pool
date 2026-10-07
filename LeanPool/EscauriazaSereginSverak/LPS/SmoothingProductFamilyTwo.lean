/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductFamily
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevGN
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools

/-!
# Products of whole-space Sobolev families at order two

At order two, the Leibniz term `∂_i f ∂_j g` pairs two first derivatives,
neither of which is bounded by the `H²` norm. The smooth Gagliardo–Nirenberg
estimate bounds this term for smooth fields; Fatou's lemma along an almost
everywhere convergent subsequence of smooth approximations transfers the bound
to whole-space Sobolev families. The other Leibniz terms contain an undifferentiated
factor, which is essentially bounded. Together with the order `m ≥ 3` case, the
product of two `H^m(ℝ³)` functions lies in `H^m(ℝ³)` for every `m ≥ 2`, with the
Leibniz family as its weak derivatives.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Along smooth `L²` approximations of a family, the squared Sobolev norms
converge. -/
private theorem lps_sobolevNormSq_tendsto_of_approx {m : ℕ} {b : ℕ → Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ}
    (hb : ∀ (n : ℕ) (α : List (Fin 3)), MemLp (wordDeriv α (b n)) 2 volume)
    (hD : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 volume)
    (hconv : ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun n => eLpNorm (wordDeriv α (b n) - D α) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => sobolevNormSqOn m univ (fun α => wordDeriv α (b n))) atTop
      (𝓝 (sobolevNormSqOn m univ D)) := by
  unfold sobolevNormSqOn
  simp only [Measure.restrict_univ]
  exact tendsto_finsetSum _ fun α hα =>
    vorticity_tendsto_integral_sq (fun n => hb n α) (hD α (mem_sobolevWords.mp hα))
      (hconv α (mem_sobolevWords.mp hα))

/-- Smooth compactly supported approximations of a whole-space family, as a
scalar sequence. -/
private theorem lps_sobolevFamily_smooth_approx_scalar {m : ℕ} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (hf : IsSobolevFamilyOn m univ f D) :
    ∃ b : ℕ → Vec3 → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (b n)) ∧ (∀ n, HasCompactSupport (b n)) ∧
      ∀ α : List (Fin 3), α.length ≤ m →
        Tendsto (fun n => eLpNorm (wordDeriv α (b n) - D α) 2 volume) atTop (𝓝 0) := by
  obtain ⟨a, ha, hac, haconv, -⟩ := sobolevFamily_smooth_approx (ι := Unit) (m := m)
    (f := fun _ => f) (D := fun α _ => D α) (fun _ => hf)
  exact ⟨fun n => a n (), fun n => ha n (), fun n => hac n (), fun α hα => haconv () α hα⟩

/-- The product of two first-order slots of whole-space `H²` families is square
integrable, bounded by the two squared `H²` norms with a universal constant
(`eq:lps-Hm-energy`). -/
theorem lps_sobolevFamily_middle_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn 2 univ f D → IsSobolevFamilyOn 2 univ g E →
      ∀ β γ : List (Fin 3), β.length = 1 → γ.length = 1 →
        MemLp (fun x => D β x * E γ x) 2 volume ∧
          ∫ x, (D β x * E γ x) ^ 2 ≤
            M * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E := by
  obtain ⟨M, hM, hmid⟩ := lps_smooth_h2_middle_product_energy
  refine ⟨M, hM, fun f g D E hf hg β γ hβ hγ => ?_⟩
  obtain ⟨b, hb, hbc, hbconv⟩ := lps_sobolevFamily_smooth_approx_scalar hf
  obtain ⟨c, hc, hcc, hcconv⟩ := lps_sobolevFamily_smooth_approx_scalar hg
  have hDmem : ∀ α : List (Fin 3), α.length ≤ 2 → MemLp (D α) 2 volume :=
    fun α hα => by simpa only [Measure.restrict_univ] using hf.memL2 α hα
  have hEmem : ∀ α : List (Fin 3), α.length ≤ 2 → MemLp (E α) 2 volume :=
    fun α hα => by simpa only [Measure.restrict_univ] using hg.memL2 α hα
  have hbmem : ∀ (n : ℕ) (α : List (Fin 3)), MemLp (wordDeriv α (b n)) 2 volume :=
    fun n α => (contDiff_wordDeriv (hb n) α).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_wordDeriv (hbc n) α)
  have hcmem : ∀ (n : ℕ) (α : List (Fin 3)), MemLp (wordDeriv α (c n)) 2 volume :=
    fun n α => (contDiff_wordDeriv (hc n) α).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_wordDeriv (hcc n) α)
  -- a common subsequence along which both first-order slots converge a.e.
  obtain ⟨ns₁, hns₁, hae₁⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
    (hbconv β (by omega))).exists_seq_tendsto_ae
  have hcconv₁ : Tendsto (fun k => eLpNorm (wordDeriv γ (c (ns₁ k)) - E γ) 2 volume)
      atTop (𝓝 0) :=
    (hcconv γ (by omega)).comp hns₁.tendsto_atTop
  obtain ⟨ns₂, hns₂, hae₂⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hcconv₁).exists_seq_tendsto_ae
  let φ : ℕ → ℕ := fun k => ns₁ (ns₂ k)
  have hφ : Tendsto φ atTop atTop := hns₁.tendsto_atTop.comp hns₂.tendsto_atTop
  have hae : ∀ᵐ x ∂volume, Tendsto
      (fun k => wordDeriv β (b (φ k)) x * wordDeriv γ (c (φ k)) x) atTop
      (𝓝 (D β x * E γ x)) := by
    filter_upwards [hae₁, hae₂] with x h₁ h₂
    exact (h₁.comp hns₂.tendsto_atTop).mul h₂
  have hmeasProd (n : ℕ) : AEStronglyMeasurable
      (fun x => wordDeriv β (b n) x * wordDeriv γ (c n) x) volume :=
    ((contDiff_wordDeriv (hb n) β).continuous.mul
      (contDiff_wordDeriv (hc n) γ).continuous).aestronglyMeasurable
  have hmeasLim : AEStronglyMeasurable (fun x => D β x * E γ x) volume :=
    (hDmem β (by omega)).aestronglyMeasurable.mul (hEmem γ (by omega)).aestronglyMeasurable
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (f := fun k x => wordDeriv β (b (φ k)) x * wordDeriv γ (c (φ k)) x)
    (fun k => hmeasProd (φ k)) _ hmeasLim hae
  -- the smooth middle bound along the approximations
  let Nb : ℕ → ℝ := fun n => sobolevNormSqOn 2 univ (fun α => wordDeriv α (b n))
  let Nc : ℕ → ℝ := fun n => sobolevNormSqOn 2 univ (fun α => wordDeriv α (c n))
  have hstep (n : ℕ) :
      eLpNorm (fun x => wordDeriv β (b n) x * wordDeriv γ (c n) x) 2 volume ≤
        ENNReal.ofReal (Real.sqrt (M * Nb n * Nc n)) := by
    obtain ⟨hint, hle⟩ := hmid (b n) (c n) (hb n) (hc n) (fun α _ => hbmem n α)
      (fun α _ => hcmem n α) β γ hβ hγ
    have hmem : MemLp (fun x => wordDeriv β (b n) x * wordDeriv γ (c n) x) 2 volume :=
      (memLp_two_iff_integrable_sq (hmeasProd n)).2 hint
    rw [vorticity_eLpNorm_two_eq_sqrt hmem]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hle)
  have hNb : Tendsto Nb atTop (𝓝 (sobolevNormSqOn 2 univ D)) :=
    lps_sobolevNormSq_tendsto_of_approx hbmem hDmem hbconv
  have hNc : Tendsto Nc atTop (𝓝 (sobolevNormSqOn 2 univ E)) :=
    lps_sobolevNormSq_tendsto_of_approx hcmem hEmem hcconv
  have hlim : Tendsto (fun k => ENNReal.ofReal (Real.sqrt (M * Nb (φ k) * Nc (φ k))))
      atTop (𝓝 (ENNReal.ofReal (Real.sqrt
        (M * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((((hNb.comp hφ).const_mul M).mul (hNc.comp hφ)).sqrt)
  have hbound : eLpNorm (fun x => D β x * E γ x) 2 volume ≤
      ENNReal.ofReal (Real.sqrt
        (M * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E)) := by
    refine hfatou.trans ?_
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun k => hstep (φ k))
  have hmem : MemLp (fun x => D β x * E γ x) 2 volume :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  have hND : 0 ≤ sobolevNormSqOn 2 univ D :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNE : 0 ≤ sobolevNormSqOn 2 univ E :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hle
  rw [vl_integral_sq_eq hmem]
  calc
    (eLpNorm (fun x => D β x * E γ x) 2 volume).toReal ^ 2 ≤
        Real.sqrt (M * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
    _ = M * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E :=
      Real.sq_sqrt (mul_nonneg (mul_nonneg hM hND) hNE)

/-- `prop:lps-smoothing` (the whole-space algebra inequality at order two): the
product of two functions in `H²(ℝ³)` lies in `H²(ℝ³)`, its ordered weak
derivatives are the Leibniz family of the two factors' families, and
`‖fg‖²_{H²} ≤ C ‖f‖²_{H²} ‖g‖²_{H²}`. -/
theorem lps_sobolevFamily_mul_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn 2 univ f D → IsSobolevFamilyOn 2 univ g E →
      IsSobolevFamilyOn 2 univ (fun x => f x * g x) (fun α => sobolevLeibnizFamily α D E) ∧
      sobolevNormSqOn 2 univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E := by
  obtain ⟨C₀, hC₀, hlow⟩ := lps_sobolevFamily_pair_bound_low (m := 2) le_rfl
  obtain ⟨M, hM, hmid⟩ := lps_sobolevFamily_middle_bound
  let S : ℝ := ∑ α ∈ sobolevWords 2, ((lpsLeibnizSplits α).length : ℝ) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun α _ => sq_nonneg _
  have hbound : ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn 2 univ f D → IsSobolevFamilyOn 2 univ g E →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (sobolevLeibnizFamily α D E) 2 volume) ∧
      sobolevNormSqOn 2 univ (fun α => sobolevLeibnizFamily α D E) ≤
        S * (C₀ ^ 2 + M) * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E := by
    intro f g D E hf hg
    have hND : 0 ≤ sobolevNormSqOn 2 univ D :=
      Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    have hNE : 0 ≤ sobolevNormSqOn 2 univ E :=
      Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    have hNN := mul_nonneg hND hNE
    obtain ⟨hmem, hnorm⟩ := lps_sobolevFamily_leibniz_normSq_le hf hg
      ((C₀ ^ 2 + M) * sobolevNormSqOn 2 univ D * sobolevNormSqOn 2 univ E)
      fun β γ hβγ => by
        by_cases hlo : β.length + 2 ≤ 2 ∨ γ.length + 2 ≤ 2
        · obtain ⟨h₁, h₂⟩ := hlow f g D E hf hg β γ hβγ hlo
          refine ⟨h₁, h₂.trans ?_⟩
          nlinarith only [mul_nonneg hM hNN]
        · obtain ⟨h₁, h₂⟩ := hmid f g D E hf hg β γ (by omega) (by omega)
          refine ⟨h₁, h₂.trans ?_⟩
          nlinarith only [mul_nonneg (sq_nonneg C₀) hNN]
    refine ⟨hmem, hnorm.trans (le_of_eq ?_)⟩
    dsimp only [S]
    ring
  exact ⟨S * (C₀ ^ 2 + M), mul_nonneg hS (add_nonneg (sq_nonneg _) hM),
    fun f g D E hf hg =>
      ⟨lps_sobolevFamily_mul_of_leibniz_bound _ hbound hf hg, (hbound f g D E hf hg).2⟩⟩

/-- `prop:lps-smoothing` (the whole-space algebra inequality): for every integer
`m ≥ 2`, the product of two functions in `H^m(ℝ³)` lies in `H^m(ℝ³)`, its ordered
weak derivatives are the Leibniz family of the two factors' families, and
`‖fg‖²_{H^m} ≤ C ‖f‖²_{H^m} ‖g‖²_{H^m}`. -/
theorem lps_sobolevFamily_mul_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → IsSobolevFamilyOn m univ g E →
      IsSobolevFamilyOn m univ (fun x => f x * g x) (fun α => sobolevLeibnizFamily α D E) ∧
      sobolevNormSqOn m univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E := by
  rcases Nat.lt_or_ge m 3 with h | h
  · obtain rfl : m = 2 := by omega
    exact lps_sobolevFamily_mul_two
  · exact lps_sobolevFamily_mul h

end ESS
