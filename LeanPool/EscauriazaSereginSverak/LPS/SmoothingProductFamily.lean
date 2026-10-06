/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEmbeddingRep
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLeibnizSplits

/-!
# Products of whole-space Sobolev families

For an integer `m ≥ 3`, the product of two functions in `H^m(ℝ³)` lies in
`H^m(ℝ³)`, its ordered weak derivatives are given by the Leibniz family of the
two factors, and `‖fg‖²_{H^m} ≤ C ‖f‖²_{H^m} ‖g‖²_{H^m}`. This is the
whole-space algebra inequality used in `prop:lps-smoothing`.

Each Leibniz term pairs two derivative orders with sum at most `m`, so one
factor has at least two orders to spare and is essentially bounded by the
embedding `H^{k+2}(ℝ³) → L^∞`. The weak Leibniz rule follows by approximating
the first factor by smooth compactly supported functions: the Leibniz family
of the difference is controlled by the same estimate. This reduction holds at
every order where the weak Leibniz estimate is available.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A slot of a whole-space Sobolev family at least two orders below `m` is
essentially bounded by the Sobolev norm of the family
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_sobolevFamily_ae_abs_le {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec3 → ℝ) (D : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → ∀ β : List (Fin 3), β.length + 2 ≤ m →
        ∀ᵐ x ∂volume, |D β x| ≤ C * Real.sqrt (sobolevNormSqOn m univ D) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C, hC, hrep⟩ := lps_sobolevFamily_contDiff_rep k
  refine ⟨C, hC, fun f D h β hβ => ?_⟩
  obtain ⟨g, -, -, hae, hbound⟩ := hrep f D h
  filter_upwards [hae β (by omega)] with x hx
  rw [← hx]
  exact hbound β (by omega) x

/-- One slot of a family contributes at most the whole squared norm. -/
private theorem lps_family_integral_sq_le_normSq {m : ℕ}
    (D : List (Fin 3) → Vec3 → ℝ) {α : List (Fin 3)} (hα : α.length ≤ m) :
    ∫ x, D α x ^ 2 ≤ sobolevNormSqOn m univ D := by
  unfold sobolevNormSqOn
  simp only [Measure.restrict_univ]
  exact Finset.single_le_sum (f := fun β : List (Fin 3) => ∫ x, D β x ^ 2)
    (fun β _ => integral_nonneg fun x => sq_nonneg _) (mem_sobolevWords.mpr hα)

/-- An essentially bounded factor times a square-integrable one. -/
private theorem lps_ae_bounded_mul_sq {a b : Vec3 → ℝ} {K : ℝ}
    (ha : AEStronglyMeasurable a volume) (hK : ∀ᵐ x ∂volume, |a x| ≤ K)
    (hb : MemLp b 2 volume) :
    MemLp (fun x => a x * b x) 2 volume ∧
      ∫ x, (a x * b x) ^ 2 ≤ K ^ 2 * ∫ x, b x ^ 2 := by
  have hprod : MemLp (fun x => a x * b x) 2 volume := by
    refine MemLp.of_le_mul (c := K) hb (ha.mul hb.aestronglyMeasurable) ?_
    filter_upwards [hK] with x hx
    change |a x * b x| ≤ K * |b x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  refine ⟨hprod, ?_⟩
  rw [← integral_const_mul]
  refine integral_mono_ae hprod.integrable_sq (hb.integrable_sq.const_mul _) ?_
  filter_upwards [hK] with x hx
  have hsq : a x ^ 2 ≤ K ^ 2 :=
    calc
      a x ^ 2 = |a x| ^ 2 := (sq_abs _).symm
      _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  calc
    (a x * b x) ^ 2 = a x ^ 2 * b x ^ 2 := by ring
    _ ≤ K ^ 2 * b x ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- A product of two slots of total order at most `m`, one of which lies at
least two orders below `m`, is square integrable, bounded by the two squared
Sobolev norms (`eq:lps-Hm-energy`). -/
theorem lps_sobolevFamily_pair_bound_low {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → IsSobolevFamilyOn m univ g E →
      ∀ β γ : List (Fin 3), β.length + γ.length ≤ m →
        (β.length + 2 ≤ m ∨ γ.length + 2 ≤ m) →
        MemLp (fun x => D β x * E γ x) 2 volume ∧
          ∫ x, (D β x * E γ x) ^ 2 ≤
            C ^ 2 * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E := by
  obtain ⟨C, hC, hae⟩ := lps_sobolevFamily_ae_abs_le hm
  refine ⟨C, hC, fun f g D E hf hg β γ hβγ hlowor => ?_⟩
  have hND : 0 ≤ sobolevNormSqOn m univ D :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNE : 0 ≤ sobolevNormSqOn m univ E :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hDmem : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 volume :=
    fun α hα => by simpa only [Measure.restrict_univ] using hf.memL2 α hα
  have hEmem : ∀ α : List (Fin 3), α.length ≤ m → MemLp (E α) 2 volume :=
    fun α hα => by simpa only [Measure.restrict_univ] using hg.memL2 α hα
  rcases hlowor with hlow | hlow'
  · obtain ⟨hmem, hint⟩ := lps_ae_bounded_mul_sq (hDmem β (by omega)).aestronglyMeasurable
      (hae f D hf β hlow) (hEmem γ (by omega))
    refine ⟨hmem, hint.trans ?_⟩
    calc
      (C * Real.sqrt (sobolevNormSqOn m univ D)) ^ 2 * ∫ x, E γ x ^ 2 ≤
          (C * Real.sqrt (sobolevNormSqOn m univ D)) ^ 2 * sobolevNormSqOn m univ E := by
        gcongr
        exact lps_family_integral_sq_le_normSq E (by omega)
      _ = C ^ 2 * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E := by
        rw [mul_pow, Real.sq_sqrt hND]
  · obtain ⟨hmem, hint⟩ := lps_ae_bounded_mul_sq (hEmem γ (by omega)).aestronglyMeasurable
      (hae g E hg γ hlow') (hDmem β (by omega))
    have hint' : ∫ x, (D β x * E γ x) ^ 2 = ∫ x, (E γ x * D β x) ^ 2 := by
      congr 1
      funext x
      ring
    refine ⟨(memLp_congr_ae (ae_of_all _ fun x => mul_comm _ _)).1 hmem, ?_⟩
    rw [hint']
    refine hint.trans ?_
    calc
      (C * Real.sqrt (sobolevNormSqOn m univ E)) ^ 2 * ∫ x, D β x ^ 2 ≤
          (C * Real.sqrt (sobolevNormSqOn m univ E)) ^ 2 * sobolevNormSqOn m univ D := by
        gcongr
        exact lps_family_integral_sq_le_normSq D (by omega)
      _ = C ^ 2 * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E := by
        rw [mul_pow, Real.sq_sqrt hNE]
        ring

/-- A Leibniz slot of measurable slots is measurable. -/
private theorem lps_leibniz_aestronglyMeasurable (α : List (Fin 3))
    (A B : List (Fin 3) → Vec3 → ℝ)
    (hA : ∀ β : List (Fin 3), β.length ≤ α.length → AEStronglyMeasurable (A β) volume)
    (hB : ∀ β : List (Fin 3), β.length ≤ α.length → AEStronglyMeasurable (B β) volume) :
    AEStronglyMeasurable (sobolevLeibnizFamily α A B) volume := by
  induction α generalizing A B with
  | nil => exact (hA [] le_rfl).mul (hB [] le_rfl)
  | cons j α ih =>
      have h1 := ih (fun β => A (j :: β)) B
        (fun β hβ => hA (j :: β) (by simp only [List.length_cons]; omega))
        (fun β hβ => hB β (by simp only [List.length_cons]; omega))
      have h2 := ih A (fun β => B (j :: β))
        (fun β hβ => hA β (by simp only [List.length_cons]; omega))
        (fun β hβ => hB (j :: β) (by simp only [List.length_cons]; omega))
      exact h1.add h2

/-- If every product of two slots of total order at most `m` is square
integrable with square integral at most `K`, then the Leibniz family of the two
families is square integrable through order `m`, and its squared Sobolev norm is
at most `K` times the number of Leibniz terms (`eq:lps-Hm-energy`). -/
theorem lps_sobolevFamily_leibniz_normSq_le {m : ℕ} {f g : Vec3 → ℝ}
    {D E : List (Fin 3) → Vec3 → ℝ}
    (hf : IsSobolevFamilyOn m univ f D) (hg : IsSobolevFamilyOn m univ g E) (K : ℝ)
    (hpair : ∀ β γ : List (Fin 3), β.length + γ.length ≤ m →
      MemLp (fun x => D β x * E γ x) 2 volume ∧ ∫ x, (D β x * E γ x) ^ 2 ≤ K) :
    (∀ α : List (Fin 3), α.length ≤ m →
      MemLp (sobolevLeibnizFamily α D E) 2 volume) ∧
    sobolevNormSqOn m univ (fun α => sobolevLeibnizFamily α D E) ≤
      (∑ α ∈ sobolevWords m, ((lpsLeibnizSplits α).length : ℝ) ^ 2) * K := by
  have hterm (α : List (Fin 3)) (hα : α.length ≤ m) :
      Integrable (fun x => sobolevLeibnizFamily α D E x ^ 2) volume ∧
        (∫ x, sobolevLeibnizFamily α D E x ^ 2) ≤
          ((lpsLeibnizSplits α).length : ℝ) ^ 2 * K :=
    lps_leibniz_integral_bound α D E K fun p hp =>
      hpair p.1 p.2 (by have := lps_leibniz_splits_degree α p hp; omega)
  have hmeasD : ∀ β : List (Fin 3), β.length ≤ m → AEStronglyMeasurable (D β) volume :=
    fun β hβ => by
      simpa only [Measure.restrict_univ] using (hf.memL2 β hβ).aestronglyMeasurable
  have hmeasE : ∀ β : List (Fin 3), β.length ≤ m → AEStronglyMeasurable (E β) volume :=
    fun β hβ => by
      simpa only [Measure.restrict_univ] using (hg.memL2 β hβ).aestronglyMeasurable
  refine ⟨fun α hα => (memLp_two_iff_integrable_sq
    (lps_leibniz_aestronglyMeasurable α D E (fun β hβ => hmeasD β (hβ.trans hα))
      (fun β hβ => hmeasE β (hβ.trans hα)))).2 (hterm α hα).1, ?_⟩
  change (∑ α ∈ sobolevWords m, ∫ x in univ, sobolevLeibnizFamily α D E x ^ 2) ≤ _
  simp only [Measure.restrict_univ]
  calc
    _ ≤ ∑ α ∈ sobolevWords m, ((lpsLeibnizSplits α).length : ℝ) ^ 2 * K :=
      Finset.sum_le_sum fun α hα => (hterm α (mem_sobolevWords.mp hα)).2
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The weak Leibniz rule on `ℝ³` (`prop:lps-smoothing`): if the Leibniz family
of any two whole-space Sobolev families of order `m` is square integrable with
the algebra bound, then the Leibniz family of `D` and `E` is a Sobolev family of
the product `f g`. The first factor is approximated by smooth compactly
supported functions, and the bound controls the Leibniz family of the
difference. -/
theorem lps_sobolevFamily_mul_of_leibniz_bound {m : ℕ} (C : ℝ)
    (hbound : ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → IsSobolevFamilyOn m univ g E →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (sobolevLeibnizFamily α D E) 2 volume) ∧
      sobolevNormSqOn m univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E)
    {f g : Vec3 → ℝ} {D E : List (Fin 3) → Vec3 → ℝ}
    (hf : IsSobolevFamilyOn m univ f D) (hg : IsSobolevFamilyOn m univ g E) :
    IsSobolevFamilyOn m univ (fun x => f x * g x)
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
  have hgE : IsSobolevFamilyOn m univ (E []) E :=
    hg.congr_ae hg.zero.symm (fun _ _ => Filter.EventuallyEq.rfl)
  -- Leibniz families of the smooth approximants times `g`
  have hprod (n : ℕ) : IsSobolevFamilyOn m univ (fun x => b n x * E [] x)
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
  -- the squared norms of the difference families tend to zero
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
  have hconv : ∀ α : List (Fin 3), α.length ≤ m →
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
    let NE := sobolevNormSqOn m univ E
    have hupper : Tendsto (fun n => Real.sqrt (C * sobolevNormSqOn m univ
        (fun α x => wordDeriv α (b n) x + (-1) * D α x) * NE)) atTop (𝓝 0) := by
      have h := ((hNdiff.const_mul C).mul_const NE).sqrt
      rwa [mul_zero, zero_mul, Real.sqrt_zero] at h
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) hupper
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    rw [← vl_integral_sq_eq (hmem n)]
    exact (lps_family_integral_sq_le_normSq
      (fun α => sobolevLeibnizFamily α (fun β x => wordDeriv β (b n) x + (-1) * D β x) E)
      hα).trans (hbound _ g _ E (hdiff n) hg).2
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

/-- `prop:lps-smoothing` (the whole-space algebra inequality): for an integer
`m ≥ 3`, the product of two functions in `H^m(ℝ³)` lies in `H^m(ℝ³)`, its ordered
weak derivatives are the Leibniz family of the two factors' families, and
`‖fg‖²_{H^m} ≤ C ‖f‖²_{H^m} ‖g‖²_{H^m}`. -/
theorem lps_sobolevFamily_mul {m : ℕ} (hm : 3 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → IsSobolevFamilyOn m univ g E →
      IsSobolevFamilyOn m univ (fun x => f x * g x) (fun α => sobolevLeibnizFamily α D E) ∧
      sobolevNormSqOn m univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E := by
  obtain ⟨C₀, hC₀, hpair⟩ := lps_sobolevFamily_pair_bound_low (m := m) (by omega)
  let S : ℝ := ∑ α ∈ sobolevWords m, ((lpsLeibnizSplits α).length : ℝ) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun α _ => sq_nonneg _
  have hbound : ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m univ f D → IsSobolevFamilyOn m univ g E →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (sobolevLeibnizFamily α D E) 2 volume) ∧
      sobolevNormSqOn m univ (fun α => sobolevLeibnizFamily α D E) ≤
        S * C₀ ^ 2 * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E := by
    intro f g D E hf hg
    obtain ⟨hmem, hnorm⟩ := lps_sobolevFamily_leibniz_normSq_le hf hg
      (C₀ ^ 2 * sobolevNormSqOn m univ D * sobolevNormSqOn m univ E)
      fun β γ hβγ => hpair f g D E hf hg β γ hβγ (by omega)
    refine ⟨hmem, hnorm.trans (le_of_eq ?_)⟩
    dsimp only [S]
    ring
  exact ⟨S * C₀ ^ 2, by positivity, fun f g D E hf hg =>
    ⟨lps_sobolevFamily_mul_of_leibniz_bound _ hbound hf hg, (hbound f g D E hf hg).2⟩⟩

end ESS
