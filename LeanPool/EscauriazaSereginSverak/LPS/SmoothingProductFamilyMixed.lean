/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductFamily
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevFour
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools

/-!
# Products of whole-space Sobolev families of mixed order

The product of a function in `H²(ℝ³)` and a function in `H¹(ℝ³)` lies in
`H¹(ℝ³)`, its first-order weak derivatives are given by the Leibniz family of the
two factors, and `‖fg‖²_{H¹} ≤ C ‖f‖²_{H²} ‖g‖²_{H¹}`. This is the mixed-order
form of the whole-space algebra inequality used in `prop:lps-smoothing`.

The undifferentiated factor `f` is essentially bounded by the embedding
`H²(ℝ³) → L^∞`. The remaining Leibniz term `∂_j f · g` pairs two functions of
`H¹(ℝ³)`; each lies in `L⁴(ℝ³)` by the whole-space Sobolev inequality and
interpolation between `L²` and `L⁶`, and Hölder's inequality bounds the product
in `L²`. The weak Leibniz rule follows by approximating `f` in `H²` by smooth
compactly supported functions.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

local instance lpsMixedHolderTripleFourFourTwo :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have hreal : Real.HolderTriple 4 4 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

/-- The zero slot and the three first-order slots of a family contribute at most
its squared first-order Sobolev norm. -/
private theorem lps_sobolevNormSq_one_ge_slots (D : List (Fin 3) → Vec3 → ℝ) :
    (∫ x, D [] x ^ 2) + ∑ k : Fin 3, ∫ x, D [k] x ^ 2 ≤ sobolevNormSqOn 1 univ D := by
  have hinj : Function.Injective (fun k : Fin 3 => [k]) := fun a b h => by
    simpa using h
  have hnot : ([] : List (Fin 3)) ∉ Finset.univ.image (fun k : Fin 3 => [k]) := by
    simp
  have hsub : insert [] (Finset.univ.image (fun k : Fin 3 => [k])) ⊆ sobolevWords 1 := by
    intro β hβ
    rw [mem_sobolevWords]
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hβ
    rcases hβ with rfl | ⟨k, rfl⟩ <;> simp
  unfold sobolevNormSqOn
  simp only [Measure.restrict_univ]
  calc
    (∫ x, D [] x ^ 2) + ∑ k : Fin 3, ∫ x, D [k] x ^ 2 =
        ∑ β ∈ insert [] (Finset.univ.image (fun k : Fin 3 => [k])), ∫ x, D β x ^ 2 := by
      rw [Finset.sum_insert hnot, Finset.sum_image (Set.injOn_of_injective hinj)]
    _ ≤ ∑ β ∈ sobolevWords 1, ∫ x, D β x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun β _ _ =>
        integral_nonneg fun x => sq_nonneg _

/-- The family of `∂_j`-derivatives of a family has squared order-`m` norm at
most the squared order-`m + 1` norm of the family. -/
private theorem lps_sobolevNormSq_cons_le (m : ℕ) (D : List (Fin 3) → Vec3 → ℝ)
    (j : Fin 3) :
    sobolevNormSqOn m univ (fun β => D (j :: β)) ≤ sobolevNormSqOn (m + 1) univ D := by
  unfold sobolevNormSqOn
  rw [← Finset.sum_image (f := fun α => ∫ x in univ, D α x ^ 2) (s := sobolevWords m)
    (g := fun β => j :: β) (Set.injOn_of_injective List.cons_injective)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun α _ _ =>
    integral_nonneg fun x => sq_nonneg _
  intro α hα
  simp only [Finset.mem_image] at hα
  obtain ⟨β, hβ, rfl⟩ := hα
  rw [mem_sobolevWords] at hβ ⊢
  simp only [List.length_cons]
  omega

/-- The zero slot of a first-order whole-space Sobolev family lies in `L⁴(ℝ³)`,
with norm at most a universal multiple of the first-order Sobolev norm: the
whole-space Sobolev inequality bounds its `L⁶` norm, and `L⁴` interpolates
between `L²` and `L⁶` (`eq:lps-Hm-energy`). -/
private theorem lps_sobolevFamily_one_eLpNorm_four_le {h : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (hD : IsSobolevFamilyOn 1 univ h D) :
    eLpNorm (D []) 4 volume ≤ (1 + gagliardoNirenbergSobolevConstant) *
      ENNReal.ofReal (Real.sqrt (sobolevNormSqOn 1 univ D)) := by
  have h0 : MemLp (D []) 2 volume := by
    simpa only [Measure.restrict_univ] using hD.memL2 [] (by simp)
  have hk (k : Fin 3) : MemLp (D [k]) 2 volume := by
    simpa only [Measure.restrict_univ] using hD.memL2 [k] (by simp)
  let v : H1Function (Set.univ : Set Vec3) :=
    { toFun := D []
      grad := fun x k => D [k] x
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using h0
      gradMemL2 := by
        intro k
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hk k
      hasWeakGradient := fun k => hD.weak [] k (by simp) }
  have hgrad : MemLp v.grad 2 volume := memLp_pi_iff.2 hk
  have h6 : eLpNorm v.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant * eLpNorm v.grad 2 volume := by
    simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
      CKN.weakGradientLpNormOn, Measure.restrict_univ] using
      (Classical.choose_spec CKN.sobolev_L6_global).2 v
  -- the Euclidean norm of the weak gradient
  let R : Vec3 → ℝ := fun x => vec3EuclideanNorm (v.grad x)
  have hRsq (x : Vec3) : R x ^ 2 = ∑ k : Fin 3, D [k] x ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hRcont : Continuous vec3EuclideanNorm :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)
  have hRmeas : AEStronglyMeasurable R volume :=
    hRcont.comp_aestronglyMeasurable hgrad.aestronglyMeasurable
  have hsqint : Integrable (fun x => ∑ k : Fin 3, D [k] x ^ 2) volume :=
    integrable_finsetSum _ fun k _ => (hk k).integrable_sq
  have hRmem : MemLp R 2 volume := by
    refine (memLp_two_iff_integrable_sq hRmeas).2 ?_
    simp_rw [hRsq]
    exact hsqint
  have hRint : ∫ x, R x ^ 2 = ∑ k : Fin 3, ∫ x, D [k] x ^ 2 := by
    simp_rw [hRsq]
    exact integral_finsetSum _ fun k _ => (hk k).integrable_sq
  have hslots := lps_sobolevNormSq_one_ge_slots D
  have hsum0 : 0 ≤ ∑ k : Fin 3, ∫ x, D [k] x ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hint0 : 0 ≤ ∫ x, D [] x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hgradle : eLpNorm v.grad 2 volume ≤
      ENNReal.ofReal (Real.sqrt (sobolevNormSqOn 1 univ D)) := by
    calc
      eLpNorm v.grad 2 volume ≤ eLpNorm R 2 volume :=
        eLpNorm_mono_real hgrad.aestronglyMeasurable fun x =>
          norm_le_vec3EuclideanNorm (v.grad x)
      _ = ENNReal.ofReal (Real.sqrt (∫ x, R x ^ 2)) := vorticity_eLpNorm_two_eq_sqrt hRmem
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by
        rw [hRint]
        linarith only [hslots, hint0]))
  have h2le : eLpNorm (D []) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (sobolevNormSqOn 1 univ D)) := by
    rw [vorticity_eLpNorm_two_eq_sqrt h0]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith only [hslots, hsum0]))
  set Z : ℝ≥0∞ := (1 + gagliardoNirenbergSobolevConstant) *
    ENNReal.ofReal (Real.sqrt (sobolevNormSqOn 1 univ D)) with hZ
  have h2Z : eLpNorm (D []) 2 volume ≤ Z :=
    h2le.trans (le_mul_of_one_le_left bot_le le_self_add)
  have h6Z : eLpNorm (D []) 6 volume ≤ Z := by
    calc
      eLpNorm (D []) 6 volume ≤
          gagliardoNirenbergSobolevConstant * eLpNorm v.grad 2 volume := h6
      _ ≤ gagliardoNirenbergSobolevConstant *
          ENNReal.ofReal (Real.sqrt (sobolevNormSqOn 1 univ D)) := by gcongr
      _ ≤ Z := by
        rw [hZ]
        gcongr
        exact le_add_self
  calc
    eLpNorm (D []) 4 volume ≤
        eLpNorm (D []) 2 volume ^ (1 / 4 : ℝ) * eLpNorm (D []) 6 volume ^ (3 / 4 : ℝ) :=
      lps_eLpNorm_four_le_two_six h0.aestronglyMeasurable
    _ ≤ Z ^ (1 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) := by gcongr
    _ = Z := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

/-- The Leibniz term `∂_j f · g` of an `H²` family and an `H¹` family is square
integrable, bounded by the two squared Sobolev norms with a universal constant,
since both factors lie in `L⁴(ℝ³)` (`eq:lps-Hm-energy`). -/
private theorem lps_sobolevFamily_mixed_middle_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn 2 univ f D → IsSobolevFamilyOn 1 univ g E → ∀ j : Fin 3,
        MemLp (fun x => D [j] x * E [] x) 2 volume ∧
          ∫ x, (D [j] x * E [] x) ^ 2 ≤
            M * sobolevNormSqOn 2 univ D * sobolevNormSqOn 1 univ E := by
  set K : ℝ≥0∞ := 1 + gagliardoNirenbergSobolevConstant with hKdef
  have hS : gagliardoNirenbergSobolevConstant ≠ ⊤ :=
    (Classical.choose_spec CKN.sobolev_L6_global).1
  have hK : K ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hS⟩
  refine ⟨K.toReal ^ 4, by positivity, fun f g D E hf hg j => ?_⟩
  set ND := sobolevNormSqOn 2 univ D with hNDdef
  set NE := sobolevNormSqOn 1 univ E with hNEdef
  have hND : 0 ≤ ND := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNE : 0 ≤ NE := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hDj : IsSobolevFamilyOn 1 univ (D [j]) (fun β => D (j :: β)) :=
    (((isSobolevFamilyOn_succ_iff (m := 1)).mp hf).2 j).2
  have hDjmeas : AEStronglyMeasurable (D [j]) volume := by
    simpa only [Measure.restrict_univ] using (hf.memL2 [j] (by simp)).aestronglyMeasurable
  have hEmeas : AEStronglyMeasurable (E []) volume := by
    simpa only [Measure.restrict_univ] using (hg.memL2 [] (by simp)).aestronglyMeasurable
  have ha : eLpNorm (D [j]) 4 volume ≤ K * ENNReal.ofReal (Real.sqrt ND) := by
    refine (lps_sobolevFamily_one_eLpNorm_four_le hDj).trans ?_
    gcongr
    exact lps_sobolevNormSq_cons_le 1 D j
  have hb : eLpNorm (E []) 4 volume ≤ K * ENNReal.ofReal (Real.sqrt NE) :=
    lps_sobolevFamily_one_eLpNorm_four_le hg
  have hsmul : (fun x => D [j] x * E [] x) = D [j] • E [] := rfl
  set X : ℝ≥0∞ := K * ENNReal.ofReal (Real.sqrt ND) * (K * ENNReal.ofReal (Real.sqrt NE))
    with hXdef
  have hX : eLpNorm (fun x => D [j] x * E [] x) 2 volume ≤ X := by
    rw [hsmul]
    exact (eLpNorm_smul_le_mul_eLpNorm hDjmeas hEmeas).trans (mul_le_mul' ha hb)
  have hXtop : X ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top)
  have hmem : MemLp (fun x => D [j] x * E [] x) 2 volume :=
    hX.trans_lt (lt_top_iff_ne_top.2 hXtop)
  refine ⟨hmem, ?_⟩
  rw [vl_integral_sq_eq hmem]
  have hle := ENNReal.toReal_mono hXtop hX
  have hXreal : X.toReal = K.toReal * Real.sqrt ND * (K.toReal * Real.sqrt NE) := by
    rw [hXdef, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  calc
    (eLpNorm (fun x => D [j] x * E [] x) 2 volume).toReal ^ 2 ≤ X.toReal ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
    _ = K.toReal ^ 4 * Real.sqrt ND ^ 2 * Real.sqrt NE ^ 2 := by
      rw [hXreal]
      ring
    _ = K.toReal ^ 4 * ND * NE := by rw [Real.sq_sqrt hND, Real.sq_sqrt hNE]

/-- The mixed-order algebra bound: the Leibniz family of an `H²` family and an
`H¹` family is square integrable through order one, with squared `H¹` norm at
most a universal multiple of the product of the two squared norms
(`eq:lps-Hm-energy`). -/
private theorem lps_sobolevFamily_mixed_leibniz_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn 2 univ f D → IsSobolevFamilyOn 1 univ g E →
      (∀ α : List (Fin 3), α.length ≤ 1 →
        MemLp (sobolevLeibnizFamily α D E) 2 volume) ∧
      sobolevNormSqOn 1 univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn 2 univ D * sobolevNormSqOn 1 univ E := by
  obtain ⟨C₀, hC₀, hae⟩ := lps_sobolevFamily_ae_abs_le (m := 2) le_rfl
  obtain ⟨M, hM, hmid⟩ := lps_sobolevFamily_mixed_middle_bound
  let S : ℝ := ∑ α ∈ sobolevWords 1, ((lpsLeibnizSplits α).length : ℝ) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun α _ => sq_nonneg _
  refine ⟨S * (C₀ ^ 2 + M), mul_nonneg hS (add_nonneg (sq_nonneg _) hM),
    fun f g D E hf hg => ?_⟩
  have hND : 0 ≤ sobolevNormSqOn 2 univ D :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNE : 0 ≤ sobolevNormSqOn 1 univ E :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNN := mul_nonneg hND hNE
  have hpair : ∀ β γ : List (Fin 3), β.length + γ.length ≤ 1 →
      MemLp (fun x => D β x * E γ x) 2 volume ∧
        ∫ x, (D β x * E γ x) ^ 2 ≤
          (C₀ ^ 2 + M) * sobolevNormSqOn 2 univ D * sobolevNormSqOn 1 univ E := by
    intro β γ hβγ
    cases β with
    | nil =>
        have hγ : γ.length ≤ 1 := by simpa using hβγ
        have hEγ : MemLp (E γ) 2 volume := by
          simpa only [Measure.restrict_univ] using hg.memL2 γ hγ
        have hD0 : AEStronglyMeasurable (D []) volume := by
          simpa only [Measure.restrict_univ] using (hf.memL2 [] (by simp)).aestronglyMeasurable
        set L : ℝ := C₀ * Real.sqrt (sobolevNormSqOn 2 univ D) with hL
        have hbd : ∀ᵐ x ∂volume, |D [] x| ≤ L := hae f D hf [] (by simp)
        have hprod : MemLp (fun x => D [] x * E γ x) 2 volume := by
          refine MemLp.of_le_mul (c := L) hEγ (hD0.mul hEγ.aestronglyMeasurable) ?_
          filter_upwards [hbd] with x hx
          change |D [] x * E γ x| ≤ L * |E γ x|
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        refine ⟨hprod, ?_⟩
        have hslot : ∫ x, E γ x ^ 2 ≤ sobolevNormSqOn 1 univ E := by
          simp only [sobolevNormSqOn, Measure.restrict_univ]
          exact Finset.single_le_sum (f := fun β : List (Fin 3) => ∫ x, E β x ^ 2)
            (fun β _ => integral_nonneg fun x => sq_nonneg _) (mem_sobolevWords.mpr hγ)
        calc
          ∫ x, (D [] x * E γ x) ^ 2 ≤ ∫ x, L ^ 2 * E γ x ^ 2 := by
            refine integral_mono_ae hprod.integrable_sq (hEγ.integrable_sq.const_mul _) ?_
            filter_upwards [hbd] with x hx
            have hsq : D [] x ^ 2 ≤ L ^ 2 :=
              calc
                D [] x ^ 2 = |D [] x| ^ 2 := (sq_abs _).symm
                _ ≤ L ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
            calc
              (D [] x * E γ x) ^ 2 = D [] x ^ 2 * E γ x ^ 2 := by ring
              _ ≤ L ^ 2 * E γ x ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
          _ = L ^ 2 * ∫ x, E γ x ^ 2 := integral_const_mul _ _
          _ ≤ L ^ 2 * sobolevNormSqOn 1 univ E := by gcongr
          _ = C₀ ^ 2 * sobolevNormSqOn 2 univ D * sobolevNormSqOn 1 univ E := by
            rw [hL, mul_pow, Real.sq_sqrt hND]
          _ ≤ _ := by nlinarith only [mul_nonneg hM hNN]
    | cons j β' =>
        simp only [List.length_cons] at hβγ
        obtain rfl : β' = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain rfl : γ = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain ⟨h₁, h₂⟩ := hmid f g D E hf hg j
        refine ⟨h₁, h₂.trans ?_⟩
        nlinarith only [mul_nonneg (sq_nonneg C₀) hNN]
  obtain ⟨hmem, hnorm⟩ := lps_sobolevFamily_leibniz_normSq_le (hf.of_le (by norm_num)) hg
    ((C₀ ^ 2 + M) * sobolevNormSqOn 2 univ D * sobolevNormSqOn 1 univ E) hpair
  refine ⟨hmem, hnorm.trans (le_of_eq ?_)⟩
  dsimp only [S]
  ring

/-- The weak Leibniz rule for Sobolev families of orders `m` and `k` on `ℝ³`: if
the Leibniz family of any order-`m` family and any order-`k` family is square
integrable through order `k` with the product bound, then the Leibniz family of
`D` and `E` is an order-`k` Sobolev family of the product `f g`. The first factor
is approximated in `H^m` by smooth compactly supported functions, and the bound
controls the Leibniz family of the difference. -/
private theorem lps_sobolevFamily_mul_of_mixed_bound {m k : ℕ} (C : ℝ)
    (hbound : ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → IsSobolevFamilyOn k univ g E →
      (∀ α : List (Fin 3), α.length ≤ k →
        MemLp (sobolevLeibnizFamily α D E) 2 volume) ∧
      sobolevNormSqOn k univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn m univ D * sobolevNormSqOn k univ E)
    {f g : Vec3 → ℝ} {D E : List (Fin 3) → Vec3 → ℝ}
    (hf : IsSobolevFamilyOn m univ f D) (hg : IsSobolevFamilyOn k univ g E) :
    IsSobolevFamilyOn k univ (fun x => f x * g x)
      (fun α => sobolevLeibnizFamily α D E) := by
  obtain ⟨a, ha, hac, haconv, -⟩ := sobolevFamily_smooth_approx (ι := Unit) (m := m)
    (f := fun _ => f) (D := fun α _ => D α) (fun _ => hf)
  obtain ⟨b, hb, hbc, hbconv⟩ : ∃ b : ℕ → Vec3 → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (b n)) ∧ (∀ n, HasCompactSupport (b n)) ∧
      ∀ α : List (Fin 3), α.length ≤ m →
        Tendsto (fun n => eLpNorm (wordDeriv α (b n) - D α) 2 volume) atTop (𝓝 0) :=
    ⟨fun n => a n (), fun n => ha n (), fun n => hac n (), fun α hα => haconv () α hα⟩
  have hDmem : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 volume :=
    fun α hα => by simpa only [Measure.restrict_univ] using hf.memL2 α hα
  have hbmem : ∀ (n : ℕ) (α : List (Fin 3)), MemLp (wordDeriv α (b n)) 2 volume :=
    fun n α => (contDiff_wordDeriv (hb n) α).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_wordDeriv (hbc n) α)
  -- the family of `g`, based at its own zero slot
  have hgE : IsSobolevFamilyOn k univ (E []) E :=
    hg.congr_ae hg.zero.symm (fun _ _ => Filter.EventuallyEq.rfl)
  -- Leibniz families of the smooth approximants times `g`
  have hprod (n : ℕ) : IsSobolevFamilyOn k univ (fun x => b n x * E [] x)
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β (b n)) E) :=
    hgE.smooth_mul isOpen_univ (hb n) fun α _ => by
      obtain ⟨L, hL⟩ := (contDiff_wordDeriv (hb n) α).continuous.bounded_above_of_compact_support
        (hasCompactSupport_wordDeriv (hbc n) α)
      exact ⟨L, fun x => by simpa only [Real.norm_eq_abs] using hL x⟩
  -- families of the differences `b n - f`
  have hdiff (n : ℕ) : IsSobolevFamilyOn m univ (fun x => b n x + (-1) * f x)
      (fun α x => wordDeriv α (b n) x + (-1) * D α x) :=
    (isSobolevFamilyOn_wordDeriv isOpen_univ (hb n) fun α _ => by
      simpa only [Measure.restrict_univ] using hbmem n α).add (hf.const_mul (-1))
  -- the Leibniz family is additive in its first argument
  have hsub : ∀ (α : List (Fin 3)) (A B F : List (Fin 3) → Vec3 → ℝ) (x : Vec3),
      sobolevLeibnizFamily α (fun β y => A β y + (-1) * B β y) F x =
        sobolevLeibnizFamily α A F x - sobolevLeibnizFamily α B F x := by
    intro α
    induction α with
    | nil =>
        intro A B F x
        simp only [sobolevLeibnizFamily]
        ring
    | cons j α ih =>
        intro A B F x
        simp only [sobolevLeibnizFamily]
        rw [ih (fun β y => A (j :: β) y) (fun β y => B (j :: β) y) F x,
          ih A B (fun β y => F (j :: β) y) x]
        ring
  -- the squared order-`m` norms of the difference families tend to zero
  have hNdiff : Tendsto (fun n => sobolevNormSqOn m univ
      (fun α x => wordDeriv α (b n) x + (-1) * D α x)) atTop (𝓝 0) := by
    have hterm : ∀ α ∈ sobolevWords m, Tendsto
        (fun n => ∫ x in univ, (wordDeriv α (b n) x + (-1) * D α x) ^ 2) atTop (𝓝 0) := by
      intro α hα
      have hαm := mem_sobolevWords.mp hα
      have hreal : Tendsto (fun n => (eLpNorm (wordDeriv α (b n) - D α) 2 volume).toReal)
          atTop (𝓝 0) :=
        (ENNReal.tendsto_toReal_zero_iff
          fun n => ((hbmem n α).sub (hDmem α hαm)).eLpNorm_ne_top).2 (hbconv α hαm)
      have heq (n : ℕ) : ∫ x in univ, (wordDeriv α (b n) x + (-1) * D α x) ^ 2 =
          (eLpNorm (wordDeriv α (b n) - D α) 2 volume).toReal ^ 2 := by
        rw [Measure.restrict_univ, ← vl_integral_sq_eq ((hbmem n α).sub (hDmem α hαm))]
        congr 1
        funext x
        simp only [Pi.sub_apply]
        ring
      rw [tendsto_congr heq]
      have h2 := hreal.pow 2
      rwa [zero_pow two_ne_zero] at h2
    have hsum := tendsto_finsetSum (sobolevWords m) hterm
    simp only [Finset.sum_const_zero] at hsum
    exact hsum
  -- the Leibniz slots of the approximants converge in `L²`
  have hconv : ∀ α : List (Fin 3), α.length ≤ k →
      Tendsto (fun n => eLpNorm (sobolevLeibnizFamily α (fun β => wordDeriv β (b n)) E -
        sobolevLeibnizFamily α D E) 2 (volume.restrict univ)) atTop (𝓝 0) := by
    intro α hα
    rw [Measure.restrict_univ]
    have hslot (n : ℕ) :
        sobolevLeibnizFamily α (fun β => wordDeriv β (b n)) E - sobolevLeibnizFamily α D E =
          sobolevLeibnizFamily α (fun β x => wordDeriv β (b n) x + (-1) * D β x) E := by
      funext x
      rw [Pi.sub_apply, hsub]
    rw [tendsto_congr fun n => congrArg (fun h => eLpNorm h 2 volume) (hslot n)]
    have hmem (n : ℕ) := (hbound _ g _ E (hdiff n) hg).1 α hα
    refine (ENNReal.tendsto_toReal_zero_iff fun n => (hmem n).eLpNorm_ne_top).1 ?_
    let NE := sobolevNormSqOn k univ E
    have hupper : Tendsto (fun n => Real.sqrt (C * sobolevNormSqOn m univ
        (fun α x => wordDeriv α (b n) x + (-1) * D α x) * NE)) atTop (𝓝 0) := by
      have h := ((hNdiff.const_mul C).mul_const NE).sqrt
      rwa [mul_zero, zero_mul, Real.sqrt_zero] at h
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hupper
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [← vl_integral_sq_eq (hmem n)]
    have hslotle : ∫ x, sobolevLeibnizFamily α
        (fun β x => wordDeriv β (b n) x + (-1) * D β x) E x ^ 2 ≤
        sobolevNormSqOn k univ (fun α => sobolevLeibnizFamily α
          (fun β x => wordDeriv β (b n) x + (-1) * D β x) E) := by
      simp only [sobolevNormSqOn, Measure.restrict_univ]
      exact Finset.single_le_sum (f := fun γ : List (Fin 3) => ∫ x, sobolevLeibnizFamily γ
          (fun β x => wordDeriv β (b n) x + (-1) * D β x) E x ^ 2)
        (fun γ _ => integral_nonneg fun x => sq_nonneg _) (mem_sobolevWords.mpr hα)
    exact hslotle.trans (hbound _ g _ E (hdiff n) hg).2
  -- pass to the limit and identify the zero slot with `f g`
  have hfam := IsSobolevFamilyOn.of_tendsto isOpen_univ
    (Dn := fun n α => sobolevLeibnizFamily α (fun β => wordDeriv β (b n)) E)
    (D := fun α => sobolevLeibnizFamily α D E) (fun n => hprod n)
    (fun α hα => by simpa only [Measure.restrict_univ] using (hbound f g D E hf hg).1 α hα)
    hconv
  refine hfam.congr_ae ?_ (fun _ _ => Filter.EventuallyEq.rfl)
  filter_upwards [hf.zero, hg.zero] with x hx hy
  change D [] x * E [] x = f x * g x
  rw [hx, hy]

/-- `prop:lps-smoothing` (the whole-space algebra inequality of mixed order): the
product of a function in `H²(ℝ³)` and a function in `H¹(ℝ³)` lies in `H¹(ℝ³)`,
its first-order weak derivatives are the Leibniz family of the two factors'
families, and `‖fg‖²_{H¹} ≤ C ‖f‖²_{H²} ‖g‖²_{H¹}`. -/
theorem lps_sobolevFamily_mul_mixed :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn 2 univ f D → IsSobolevFamilyOn 1 univ g E →
      IsSobolevFamilyOn 1 univ (fun x => f x * g x) (fun α => sobolevLeibnizFamily α D E) ∧
      sobolevNormSqOn 1 univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn 2 univ D * sobolevNormSqOn 1 univ E := by
  obtain ⟨C, hC, hbound⟩ := lps_sobolevFamily_mixed_leibniz_bound
  exact ⟨C, hC, fun f g D E hf hg =>
    ⟨lps_sobolevFamily_mul_of_mixed_bound C hbound hf hg, (hbound f g D E hf hg).2⟩⟩

end ESS
