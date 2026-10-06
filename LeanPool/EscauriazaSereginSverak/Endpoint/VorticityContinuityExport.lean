/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityFinalBound
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticitySliceWeakLimit

/-!
# The vorticity representative and time-slice Sobolev export

A field solving a heat equation with square-integrable flux, whose first and second spatial
weak derivatives solve heat equations of the same kind, has a representative which is continuous
and bounded up to the top time on a smaller closed box: at every time the backward mollifications
are Cauchy in the uniform norm, by the `H²` embedding and the uniform-in-time `L²` Cauchy property
of the mollified fields (the continuity statement of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private def vorticityContinuityExportHeatWeak (W : Set (Vec3 × ℝ))
    (q : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ) : Prop :=
  ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ W →
    ∫ y in W, q y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
      -∫ y in W, ∑ j : Fin 3, F j y * spatialPartial ψ j y

private structure VorticityContinuityExportHeatControl
    (x₀ : Vec3) (t₀ a Ch : ℝ) (W : Set (Vec3 × ℝ))
    (bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ) where
  squareBound : ∀ (q : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ),
    MemLp q 2 (volume.restrict W) →
    (∀ j, MemLp (F j) 2 (volume.restrict W)) →
    vorticityContinuityExportHeatWeak W q F →
    ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm q n (x, t) ^ 2 ≤
        Ch * (∫ y in W, (q y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) + 1
  pairCauchy : ∀ (q : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ),
    MemLp q 2 (volume.restrict W) →
    (∀ j, MemLp (F j) 2 (volume.restrict W)) →
    vorticityContinuityExportHeatWeak W q F →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)),
      ∀ t ∈ Icc (a + 1 / 64) t₀,
        ∫ x in vec3Ball x₀ (42 / 64),
          (bm q p.1 (x, t) - bm q p.2 (x, t)) ^ 2 ≤ δ

private theorem vorticityContinuityExport_uniformCauchyLimit
    (x₀ : Vec3) (a t₀ Cs A : ℝ)
    (bm : ℕ → Vec3 × ℝ → ℝ)
    (hbmContinuous : ∀ n, Continuous (bm n))
    (hbound : ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x,
      vec3EuclideanNorm (x - x₀) ≤ 38 / 64 → bm n (x, t) ^ 2 ≤ Cs * (13 * A))
    (hcauchy : ∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)),
      ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x, vec3EuclideanNorm (x - x₀) ≤ 38 / 64 →
        (bm p.1 (x, t) - bm p.2 (x, t)) ^ 2 ≤ Cs * (13 * δ)) :
    ∃ ω : Vec3 × ℝ → ℝ,
      ContinuousOn ω ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ
        Icc (a + 1 / 64) t₀) ∧
      (∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ
        Icc (a + 1 / 64) t₀ : Set (Vec3 × ℝ)), |ω z| ≤ Real.sqrt (Cs * (13 * A))) ∧
      (∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ
        Icc (a + 1 / 64) t₀ : Set (Vec3 × ℝ)),
        Tendsto (fun n => bm n z) atTop (𝓝 (ω z))) ∧
      TendstoUniformlyOn bm ω atTop
        ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ
          Icc (a + 1 / 64) t₀) := by
  let K := ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ
    Icc (a + 1 / 64) t₀ : Set (Vec3 × ℝ))
  have hUC : UniformCauchySeqOn bm atTop K := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro η hη
    have hne : (13 * Cs + 1) ≠ 0 := by positivity
    have hδ : 0 < η ^ 2 / (2 * (13 * Cs + 1)) := by positivity
    obtain ⟨⟨N1, N2⟩, hN⟩ := eventually_atTop.1
      (hcauchy _ hδ)
    refine ⟨max N1 N2, fun m hm n hn z hz => ?_⟩
    obtain ⟨x, t⟩ := z
    have hb := hN (m, n) ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hn⟩
      t hz.2 x hz.1
    have e1 : (13 * Cs + 1) * (η ^ 2 / (2 * (13 * Cs + 1))) = η ^ 2 / 2 := by
      rw [mul_div_assoc', div_eq_div_iff (by positivity) (by norm_num)]
      ring
    have e2 : (13 * Cs + 1) * (η ^ 2 / (2 * (13 * Cs + 1))) =
        Cs * (13 * (η ^ 2 / (2 * (13 * Cs + 1)))) + η ^ 2 / (2 * (13 * Cs + 1)) := by
      ring
    have hη2 : 0 < η ^ 2 := by positivity
    rw [Real.dist_eq]
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hb (by linarith only [e1, e2, hδ, hη2])) hη.le
  have hlim : ∀ z ∈ K, Tendsto (fun n => bm n z) atTop
      (𝓝 (limUnder atTop (fun n => bm n z))) := fun z hz =>
    (hUC.cauchySeq hz).tendsto_limUnder
  let ω : Vec3 × ℝ → ℝ := fun z => limUnder atTop (fun n => bm n z)
  have hTU : TendstoUniformlyOn bm ω atTop K := hUC.tendstoUniformlyOn_of_tendsto hlim
  have hωcontinuous := hTU.continuousOn
    (Frequently.of_forall fun n => (hbmContinuous n).continuousOn)
  have hωbounded : ∀ z ∈ K, |ω z| ≤ Real.sqrt (Cs * (13 * A)) := by
    rintro ⟨x, t⟩ hz
    have hsq := ((continuous_pow 2).tendsto _).comp (hlim _ hz)
    exact Real.abs_le_sqrt (le_of_tendsto hsq (hbound.mono fun n hn => hn t hz.2 x hz.1))
  exact ⟨ω, hωcontinuous, hωbounded, hlim, hTU⟩

private theorem vorticityContinuityExport_sliceSobolevBound
  (x₀ : Vec3) (Cs : ℝ) : ∀ (f : Vec3 × ℝ → ℝ) (gg : Fin 3 → Vec3 × ℝ → ℝ)
    (hh : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (t B : ℝ),
    ContDiff ℝ (⊤ : ℕ∞) f → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (gg j)) →
    (∀ j k, Continuous (hh j k)) →
    (∀ x ∈ vec3Ball x₀ (42 / 64), ∀ j, spatialPartial f j (x, t) = gg j (x, t)) →
    (∀ x ∈ vec3Ball x₀ (42 / 64), ∀ j k, spatialPartial (gg j) k (x, t) = hh j k (x, t)) →
    ∫ x in vec3Ball x₀ (42 / 64), f (x, t) ^ 2 ≤ B →
    (∀ j, ∫ x in vec3Ball x₀ (42 / 64), gg j (x, t) ^ 2 ≤ B) →
    (∀ j k, ∫ x in vec3Ball x₀ (42 / 64), hh j k (x, t) ^ 2 ≤ B) →
    ∀ x, vec3EuclideanNorm (x - x₀) ≤ 38 / 64 → f (x, t) ^ 2 ≤ Cs * (13 * B)  := by
  intro f gg hh t B hf hgg hhh hfg hgh hB1 hB2 hB3 x hx
  refine (hsob x₀ t f gg hf hgg hfg x hx).trans (mul_le_mul_of_nonneg_left ?_ hCs)
  have cf : Continuous (fun y : Vec3 => f (y, t) ^ 2) := (hsl _ hf.continuous t).pow 2
  have cg : ∀ j, Continuous (fun y : Vec3 => gg j (y, t) ^ 2) := fun j =>
    (hsl _ (hgg j).continuous t).pow 2
  have ch : ∀ j k, Continuous (fun y : Vec3 => hh j k (y, t) ^ 2) := fun j k =>
    (hsl _ (hhh j k) t).pow 2
  have sg : Continuous (fun y : Vec3 => ∑ j : Fin 3, gg j (y, t) ^ 2) :=
    continuous_finsetSum _ fun j _ => cg j
  have sh : Continuous (fun y : Vec3 => ∑ j : Fin 3, ∑ k : Fin 3, hh j k (y, t) ^ 2) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ch j k
  have e : ∫ y in vec3Ball x₀ (42 / 64), (f (y, t) ^ 2 + ∑ j : Fin 3, gg j (y, t) ^ 2 +
        ∑ j : Fin 3, ∑ k : Fin 3, spatialPartial (gg j) k (y, t) ^ 2) =
      ∫ y in vec3Ball x₀ (42 / 64), (f (y, t) ^ 2 + ∑ j : Fin 3, gg j (y, t) ^ 2 +
        ∑ j : Fin 3, ∑ k : Fin 3, hh j k (y, t) ^ 2) :=
    setIntegral_congr_fun (isOpen_vec3Ball x₀ _).measurableSet fun y hy => by
      simp only [hgh y hy]
  have cfg : Continuous (fun y : Vec3 => f (y, t) ^ 2 + ∑ j : Fin 3, gg j (y, t) ^ 2) :=
    cf.add sg
  rw [e, integral_add (hib _ cfg) (hib _ sh), integral_add (hib _ cf) (hib _ sg),
    integral_finsetSum _ fun j _ => hib _ (cg j),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hib _ (ch j k)]
  have h2 : ∑ j : Fin 3, ∫ y in vec3Ball x₀ (42 / 64), gg j (y, t) ^ 2 ≤ 3 * B := by
    calc
      _ ≤ ∑ _j : Fin 3, B := Finset.sum_le_sum fun j _ => hB2 j
      _ = 3 * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  have h3 : ∑ j : Fin 3, ∫ y in vec3Ball x₀ (42 / 64), ∑ k : Fin 3, hh j k (y, t) ^ 2 ≤
      9 * B := by
    calc
      _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, B := Finset.sum_le_sum fun j _ => by
        rw [integral_finsetSum _ fun k _ => hib _ (ch j k)]
        exact Finset.sum_le_sum fun k _ => hB3 j k
      _ = 9 * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  linarith only [hB1, h2, h3]

private theorem vorticityContinuityExport_limitSliceDerivatives
    {Bs : Set Vec3} (ωt : Vec3 → ℝ) (f : ℕ → Vec3 → ℝ)
    (g : Fin 3 → ℕ → Vec3 → ℝ) (h : Fin 3 → Fin 3 → ℕ → Vec3 → ℝ)
    (G : Fin 3 → Vec3 → ℝ) (H : Fin 3 → Fin 3 → Vec3 → ℝ) (A : ℝ)
    (hBsmeas : MeasurableSet Bs)
    (hfSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hgSmooth : ∀ j n, ContDiff ℝ (⊤ : ℕ∞) (g j n))
    (hfmem : ∀ n, MemLp (f n) 2 (volume.restrict Bs))
    (hgmem : ∀ j n, MemLp (g j n) 2 (volume.restrict Bs))
    (hhmem : ∀ j k n, MemLp (h j k n) 2 (volume.restrict Bs))
    (hωmem : MemLp ωt 2 (volume.restrict Bs))
    (hGmem : ∀ j, MemLp (G j) 2 (volume.restrict Bs))
    (hHmem : ∀ j k, MemLp (H j k) 2 (volume.restrict Bs))
    (hωconv : Tendsto (fun n => eLpNorm (fun x => f n x - ωt x) 2
      (volume.restrict Bs)) atTop (𝓝 0))
    (hGconv : ∀ j, Tendsto (fun n => eLpNorm (fun x => g j n x - G j x) 2
      (volume.restrict Bs)) atTop (𝓝 0))
    (hHconv : ∀ j k, Tendsto (fun n => eLpNorm (fun x => h j k n x - H j k x) 2
      (volume.restrict Bs)) atTop (𝓝 0))
    (hderivF : ∀ n x, x ∈ Bs → ∀ j, spatialDeriv (f n) j x = g j n x)
    (hderivG : ∀ n x, x ∈ Bs → ∀ j k, spatialDeriv (g j n) k x = h j k n x)
    (hωbound : ∫ x in Bs, ωt x ^ 2 ≤ A)
    (hGbound : ∀ j, ∫ x in Bs, G j x ^ 2 ≤ A)
    (hHbound : ∀ j k, ∫ x in Bs, H j k x ^ 2 ≤ A) :
    (∀ j, HasWeakPartialDerivOn Bs j ωt (G j)) ∧
    (∀ j k, HasWeakPartialDerivOn Bs k (G j) (H j k)) ∧
    ∫ x in Bs, (ωt x ^ 2 + ∑ j : Fin 3, G j x ^ 2 +
      ∑ j : Fin 3, ∑ k : Fin 3, H j k x ^ 2) ≤ 13 * A := by
  have hfirst : ∀ j, HasWeakPartialDerivOn Bs j ωt (G j) := by
    intro j
    apply vorticity_sliceWeakPartial_of_tendsto hBsmeas
      (fun n => hfSmooth n) hfmem (fun n => hgmem j n)
      hωmem (hGmem j) hωconv (hGconv j)
    intro n x hx
    exact hderivF n x hx j
  have hsecond : ∀ j k, HasWeakPartialDerivOn Bs k (G j) (H j k) := by
    intro j k
    apply vorticity_sliceWeakPartial_of_tendsto hBsmeas
      (fun n => hgSmooth j n) (fun n => hgmem j n) (fun n => hhmem j k n)
      (hGmem j) (hHmem j k) (hGconv j) (hHconv j k)
    intro n x hx
    exact hderivG n x hx j k
  have hωsq : IntegrableOn (fun x : Vec3 => ωt x ^ 2) Bs :=
    (memLp_two_iff_integrable_sq hωmem.aestronglyMeasurable).1 hωmem
  have hGsq : ∀ j, IntegrableOn (fun x : Vec3 => G j x ^ 2) Bs := fun j =>
    (memLp_two_iff_integrable_sq (hGmem j).aestronglyMeasurable).1 (hGmem j)
  have hHsq : ∀ j k, IntegrableOn (fun x : Vec3 => H j k x ^ 2) Bs := fun j k =>
    (memLp_two_iff_integrable_sq (hHmem j k).aestronglyMeasurable).1 (hHmem j k)
  have hGsum : ∑ j : Fin 3, ∫ x in Bs, G j x ^ 2 ≤ 3 * A := by
    calc _ ≤ ∑ _j : Fin 3, A := Finset.sum_le_sum fun j _ => hGbound j
      _ = 3 * A := by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hHsum : ∑ j : Fin 3, ∑ k : Fin 3, ∫ x in Bs, H j k x ^ 2 ≤ 9 * A := by
    calc _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, A := Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => hHbound j k
      _ = 9 * A := by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]; ring
  refine ⟨hfirst, hsecond, ?_⟩
  have hGs : IntegrableOn (fun x : Vec3 => ∑ j : Fin 3, G j x ^ 2) Bs :=
    integrable_finsetSum _ fun j _ => hGsq j
  have hHs : IntegrableOn
      (fun x : Vec3 => ∑ j : Fin 3, ∑ k : Fin 3, H j k x ^ 2) Bs :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hHsq j k
  rw [integral_add (hωsq.add hGs).integrable hHs.integrable,
    integral_add hωsq.integrable hGs.integrable,
    integral_finsetSum _ fun j _ => hGsq j]
  have hHsumInt : (∫ x in Bs, ∑ j : Fin 3, ∑ k : Fin 3, H j k x ^ 2) =
      ∑ j : Fin 3, ∑ k : Fin 3, ∫ x in Bs, H j k x ^ 2 := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hHsq j k]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hHsq j k
  rw [hHsumInt]
  calc _ ≤ A + 3 * A + 9 * A := add_le_add (add_le_add hωbound hGsum) hHsum
    _ = 13 * A := by ring

private theorem vorticityContinuityExport_l2LimitFromCauchy
    {Bs : Set Vec3} (f : ℕ → Vec3 → ℝ) (A : ℝ)
    (hmem : ∀ n, MemLp (f n) 2 (volume.restrict Bs))
    (hpairInt : Tendsto (fun p : ℕ × ℕ =>
      ∫ x in Bs, (f p.1 x - f p.2 x) ^ 2) atTop (𝓝 0))
    (happrox : ∀ᶠ n in atTop, ∫ x in Bs, f n x ^ 2 ≤ A) :
    ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - Q x) 2 (volume.restrict Bs)) atTop (𝓝 0) ∧
      (∫ x in Bs, Q x ^ 2) ≤ A := by
  have hpairMem : ∀ p : ℕ × ℕ,
      MemLp (fun x : Vec3 => f p.1 x - f p.2 x) 2 (volume.restrict Bs) := fun p =>
    (hmem p.1).sub (hmem p.2)
  have hpairConv := vorticity_tendsto_eLpNorm_of_integral_sq hpairMem hpairInt
  obtain ⟨Q, hQmem, hQconv⟩ := vorticityL2_exists_limit hmem hpairConv
  have hQsq := vorticity_tendsto_integral_sq hmem hQmem hQconv
  have hQbound : (∫ x in Bs, Q x ^ 2) ≤ A := by
    apply le_of_tendsto_of_tendsto hQsq tendsto_const_nhds
    exact happrox
  exact ⟨Q, hQmem, hQconv, hQbound⟩

private theorem vorticityContinuityExport_controlledMollificationIntegrals
    {W : Set (Vec3 × ℝ)} (x₀ : Vec3) (a t₀ Ch Kw K1 K2 : ℝ) (hCh : 0 ≤ Ch)
    (bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ)
    (control : VorticityContinuityExportHeatControl x₀ t₀ a Ch W bm)
    (w : Vec3 × ℝ → ℝ) (g : Fin 3 → Vec3 × ℝ → ℝ)
    (h : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (Fw : Fin 3 → Vec3 × ℝ → ℝ) (Fg : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (Fh : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hw : MemLp w 2 (volume.restrict W))
    (hg : ∀ m, MemLp (g m) 2 (volume.restrict W))
    (hh : ∀ m k, MemLp (h m k) 2 (volume.restrict W))
    (hFw : ∀ j, MemLp (Fw j) 2 (volume.restrict W))
    (hFg : ∀ m j, MemLp (Fg m j) 2 (volume.restrict W))
    (hFh : ∀ m k j, MemLp (Fh m k j) 2 (volume.restrict W))
    (hheatw : vorticityContinuityExportHeatWeak W w Fw)
    (hheatg : ∀ m, vorticityContinuityExportHeatWeak W (g m) (Fg m))
    (hheath : ∀ m k, vorticityContinuityExportHeatWeak W (h m k) (Fh m k))
    (hKw : ∫ y in W, (w y ^ 2 + ∑ j : Fin 3, Fw j y ^ 2) ≤ Kw)
    (hK1 : ∀ m, ∫ y in W, (g m y ^ 2 + ∑ j : Fin 3, Fg m j y ^ 2) ≤ K1)
    (hK2 : ∀ m k, ∫ y in W, (h m k y ^ 2 + ∑ j : Fin 3, Fh m k j y ^ 2) ≤ K2) :
    (∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm w n (x, t) ^ 2 ≤ Ch *
        (|Kw| + |K1| + |K2|) + 1) ∧
    (∀ᶠ n in atTop, ∀ m, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (g m) n (x, t) ^ 2 ≤ Ch *
        (|Kw| + |K1| + |K2|) + 1) ∧
    (∀ᶠ n in atTop, ∀ m k, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (h m k) n (x, t) ^ 2 ≤ Ch *
        (|Kw| + |K1| + |K2|) + 1) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), (bm w p.1 (x, t) - bm w p.2 (x, t)) ^ 2 ≤ δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ∀ m,
      ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64),
        (bm (g m) p.1 (x, t) - bm (g m) p.2 (x, t)) ^ 2 ≤ δ) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ∀ m k,
      ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64),
        (bm (h m k) p.1 (x, t) - bm (h m k) p.2 (x, t)) ^ 2 ≤ δ) := by
  have hA1 : ∀ X : ℝ, X ≤ |Kw| + |K1| + |K2| → Ch * X + 1 ≤
      Ch * (|Kw| + |K1| + |K2|) + 1 := fun X hX => by
    exact add_le_add (mul_le_mul_of_nonneg_left hX hCh) le_rfl
  have hboundW := control.squareBound w Fw hw hFw hheatw
  have hboundG : ∀ m, ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (g m) n (x, t) ^ 2 ≤
        Ch * (∫ y in W, (g m y ^ 2 + ∑ j : Fin 3, Fg m j y ^ 2)) + 1 := fun m =>
    control.squareBound (g m) (Fg m) (hg m) (hFg m) (hheatg m)
  have hboundH : ∀ m k, ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (42 / 64), bm (h m k) n (x, t) ^ 2 ≤
        Ch * (∫ y in W, (h m k y ^ 2 + ∑ j : Fin 3, Fh m k j y ^ 2)) + 1 := fun m k =>
    control.squareBound (h m k) (Fh m k) (hh m k) (hFh m k) (hheath m k)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hboundW] with n hn t ht
    exact (hn t ht).trans (hA1 _ (by linarith only [hKw, le_abs_self Kw]))
  · rw [eventually_all]
    intro m
    filter_upwards [hboundG m] with n hn t ht
    exact (hn t ht).trans (hA1 _ (by linarith only [hK1 m, le_abs_self K1]))
  · rw [eventually_all]
    intro m
    rw [eventually_all]
    intro k
    filter_upwards [hboundH m k] with n hn t ht
    exact (hn t ht).trans (hA1 _ (by linarith only [hK2 m k, le_abs_self K2]))
  · exact control.pairCauchy w Fw hw hFw hheatw
  · intro δ hδ
    rw [eventually_all]
    intro m
    exact control.pairCauchy (g m) (Fg m) (hg m) (hFg m) (hheatg m) δ hδ
  · intro δ hδ
    rw [eventually_all]
    intro m
    rw [eventually_all]
    intro k
    exact control.pairCauchy (h m k) (Fh m k) (hh m k) (hFh m k) (hheath m k) δ hδ

private theorem vorticityContinuityExport_sliceMollificationLimit
    {W : Set (Vec3 × ℝ)} {Bs : Set Vec3}
    (x₀ : Vec3) (a t₀ t Ch A : ℝ) (ht : t ∈ Icc (a + 1 / 64) t₀)
    (bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ)
    (control : VorticityContinuityExportHeatControl x₀ t₀ a Ch W bm)
    (q : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ)
    (hq : MemLp q 2 (volume.restrict W))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict W))
    (hheat : vorticityContinuityExportHeatWeak W q F)
    (henergy : Ch * (∫ y in W, (q y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) + 1 ≤ A)
    (hsmem : ∀ n, MemLp (fun x : Vec3 => bm q n (x, t)) 2 (volume.restrict Bs))
    (hcontinuous : ∀ n, Continuous (fun x : Vec3 => bm q n (x, t)))
    (hBsmeas : MeasurableSet Bs) (hBs42 : Bs ⊆ vec3Ball x₀ (42 / 64)) :
    ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
      Tendsto (fun n => eLpNorm (fun x : Vec3 => bm q n (x, t) - Q x) 2
        (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A := by
  have hpairInt : Tendsto (fun p : ℕ × ℕ =>
      ∫ x in Bs, (bm q p.1 (x, t) - bm q p.2 (x, t)) ^ 2) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      filter_upwards [] with p
      exact lt_of_lt_of_le hb (setIntegral_nonneg hBsmeas fun x hx => sq_nonneg _)
    · intro δ hδ
      have hδ2 : 0 < δ / 2 := by positivity
      filter_upwards [control.pairCauchy q F hq hF hheat (δ / 2) hδ2] with p hp
      have hdcont : Continuous (fun x : Vec3 =>
          bm q p.1 (x, t) - bm q p.2 (x, t)) := (hcontinuous p.1).sub (hcontinuous p.2)
      have hmono := setIntegral_mono_set
        (vorticityHeatSmooth_integrableOn_ball (hdcont.pow 2) x₀ (42 / 64))
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hBs42)
      exact lt_of_le_of_lt (hmono.trans (hp t ht)) (by linarith only [hδ])
  have happrox : ∀ᶠ n in atTop, ∫ x in Bs, bm q n (x, t) ^ 2 ≤ A := by
    filter_upwards [control.squareBound q F hq hF hheat] with n hn
    have hnt := hn n t ht
    have hcont : Continuous (fun x : Vec3 => bm q n (x, t) ^ 2) := (hcontinuous n).pow 2
    exact (setIntegral_mono_set
      (vorticityHeatSmooth_integrableOn_ball hcont x₀ (42 / 64))
      (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hBs42)).trans
      (hnt.trans henergy)
  exact vorticityContinuityExport_l2LimitFromCauchy (fun n x => bm q n (x, t)) A
    (fun n => hsmem n) hpairInt happrox

private theorem vorticityContinuityExport_identifyTimeSliceLimit
    {Bs : Set Vec3} (f : ℕ → Vec3 → ℝ) (Q q : Vec3 → ℝ)
    (hBsmeas : MeasurableSet Bs)
    (hfmem : ∀ n, MemLp (f n) 2 (volume.restrict Bs))
    (hQmem : MemLp Q 2 (volume.restrict Bs))
    (hQconv : Tendsto (fun n => eLpNorm (fun x => f n x - Q x) 2
      (volume.restrict Bs)) atTop (𝓝 0))
    (hpointwise : ∀ x, x ∈ Bs → Tendsto (fun n => f n x) atTop (𝓝 (q x))) :
    Q =ᵐ[volume.restrict Bs] q := by
  obtain ⟨φ, hφ, hae⟩ := vorticity_exists_subseq_ae (μ := volume.restrict Bs)
    (ι := Unit) (f := fun _ n x => f n x) (F := fun _ => Q)
    (fun _ n => hfmem n) (fun _ => hQmem) (fun _ => hQconv)
  filter_upwards [hae, ae_restrict_mem hBsmeas] with x hx hxb
  exact (tendsto_nhds_unique ((hpointwise x hxb).comp hφ.tendsto_atTop) (hx ())).symm

private theorem vorticityContinuityExport_stageTimeSliceLimits
    {W : Set (Vec3 × ℝ)} {Bs : Set Vec3}
    (x₀ : Vec3) (t A Kw K1 K2 : ℝ)
    (bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ)
    (stageLimit : ∀ (q : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ),
      MemLp q 2 (volume.restrict W) →
      (∀ j, MemLp (F j) 2 (volume.restrict W)) →
      vorticityContinuityExportHeatWeak W q F →
      (∫ y in W, (q y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) ≤
        |Kw| + |K1| + |K2| →
      ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
        Tendsto (fun n => eLpNorm (fun x : Vec3 => bm q n (x, t) - Q x) 2
          (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A)
    (w : Vec3 × ℝ → ℝ) (g : Fin 3 → Vec3 × ℝ → ℝ)
    (h : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (Fw : Fin 3 → Vec3 × ℝ → ℝ) (Fg : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (Fh : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hw : MemLp w 2 (volume.restrict W))
    (hg : ∀ m, MemLp (g m) 2 (volume.restrict W))
    (hh : ∀ m k, MemLp (h m k) 2 (volume.restrict W))
    (hFw : ∀ j, MemLp (Fw j) 2 (volume.restrict W))
    (hFg : ∀ m j, MemLp (Fg m j) 2 (volume.restrict W))
    (hFh : ∀ m k j, MemLp (Fh m k j) 2 (volume.restrict W))
    (hheatw : vorticityContinuityExportHeatWeak W w Fw)
    (hheatg : ∀ m, vorticityContinuityExportHeatWeak W (g m) (Fg m))
    (hheath : ∀ m k, vorticityContinuityExportHeatWeak W (h m k) (Fh m k))
    (hKw : ∫ y in W, (w y ^ 2 + ∑ j : Fin 3, Fw j y ^ 2) ≤ Kw)
    (hK1 : ∀ m, ∫ y in W, (g m y ^ 2 + ∑ j : Fin 3, Fg m j y ^ 2) ≤ K1)
    (hK2 : ∀ m k, ∫ y in W, (h m k y ^ 2 + ∑ j : Fin 3, Fh m k j y ^ 2) ≤ K2) :
    (∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
      Tendsto (fun n => eLpNorm (fun x : Vec3 => bm w n (x, t) - Q x) 2
        (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A) ∧
    (∀ m, ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
      Tendsto (fun n => eLpNorm (fun x : Vec3 => bm (g m) n (x, t) - Q x) 2
        (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A) ∧
    (∀ m k, ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
      Tendsto (fun n => eLpNorm (fun x : Vec3 => bm (h m k) n (x, t) - Q x) 2
        (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A) := by
  have hKw' : ∫ y in W, (w y ^ 2 + ∑ j : Fin 3, Fw j y ^ 2) ≤ |Kw| + |K1| + |K2| := by
    calc
      _ ≤ Kw := hKw
      _ ≤ |Kw| := le_abs_self Kw
      _ ≤ |Kw| + |K1| + |K2| := by
        calc
          |Kw| ≤ |Kw| + |K1| := le_add_of_nonneg_right (abs_nonneg K1)
          _ ≤ |Kw| + |K1| + |K2| := le_add_of_nonneg_right (abs_nonneg K2)
  have hK1' : ∀ m, ∫ y in W, (g m y ^ 2 + ∑ j : Fin 3, Fg m j y ^ 2) ≤
      |Kw| + |K1| + |K2| := by
    intro m
    calc
      _ ≤ K1 := hK1 m
      _ ≤ |K1| := le_abs_self K1
      _ ≤ |Kw| + |K1| := le_add_of_nonneg_left (abs_nonneg Kw)
      _ ≤ |Kw| + |K1| + |K2| := le_add_of_nonneg_right (abs_nonneg K2)
  have hK2' : ∀ m k, ∫ y in W, (h m k y ^ 2 + ∑ j : Fin 3, Fh m k j y ^ 2) ≤
      |Kw| + |K1| + |K2| := by
    intro m k
    calc
      _ ≤ K2 := hK2 m k
      _ ≤ |K2| := le_abs_self K2
      _ ≤ |K1| + |K2| := le_add_of_nonneg_left (abs_nonneg K1)
      _ ≤ |Kw| + (|K1| + |K2|) := le_add_of_nonneg_left (abs_nonneg Kw)
      _ = |Kw| + |K1| + |K2| := by ring
  exact ⟨stageLimit w Fw hw hFw hheatw hKw',
    fun m => stageLimit (g m) (Fg m) (hg m) (hFg m) (hheatg m) (hK1' m),
    fun m k => stageLimit (h m k) (Fh m k) (hh m k) (hFh m k) (hheath m k) (hK2' m k)⟩

/-- A continuous representative and uniform time-slice `H²` data from heat equations for the field
and its first and second spatial weak derivatives. -/
theorem vorticity_continuousRep_export (Kw K1 K2 : ℝ) :
    ∃ C Cslice : ℝ, 0 ≤ C ∧ 0 ≤ Cslice ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (w : Vec3 × ℝ → ℝ)
      (g Fw : Fin 3 → Vec3 × ℝ → ℝ) (h Fg : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (Fh : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    a + 1 / 64 < t₀ → t₀ ≤ a + 1 →
    MemLp w 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀)) →
    (∀ m, MemLp (g m) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ m k, MemLp (h m k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ j, MemLp (Fw j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ m j, MemLp (Fg m j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ m k j, MemLp (Fh m k j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀))) →
    (∀ j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, w y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, g j y * ψ y) →
    (∀ m k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, g m y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, h m k y * ψ y) →
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, ∑ j : Fin 3, Fw j y * spatialPartial ψ j y) →
    (∀ m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          g m y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, Fg m j y * spatialPartial ψ j y) →
    (∀ m k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          h m k y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, Fh m k j y * spatialPartial ψ j y) →
    (∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀, (w y ^ 2 + ∑ j : Fin 3, Fw j y ^ 2)) ≤ Kw →
    (∀ m, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (g m y ^ 2 + ∑ j : Fin 3, Fg m j y ^ 2) ≤ K1) →
    (∀ m k, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀,
      (h m k y ^ 2 + ∑ j : Fin 3, Fh m k j y ^ 2) ≤ K2) →
    ∃ ε : ℕ → ℝ, ∃ hεpos : ∀ n, 0 < ε n, ∃ ω : Vec3 × ℝ → ℝ,
      ContinuousOn ω ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀) ∧
      (∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀ :
        Set (Vec3 × ℝ)), |ω z| ≤ C) ∧
      ω =ᵐ[volume.restrict (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀)] w ∧
      TendstoUniformlyOn
        (fun n z => vorticityBackMollify (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀) w
          (ε n) (hεpos n) z) ω atTop
        ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀) ∧
      ∀ t ∈ Icc (a + 1 / 64) t₀, ∃ G : Fin 3 → Vec3 → ℝ, ∃ H : Fin 3 → Fin 3 → Vec3 → ℝ,
        (∀ j, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) j
          (fun x => ω (x, t)) (G j)) ∧
        (∀ j k, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) k
          (G j) (H j k)) ∧
        ∫ x in vec3Ball x₀ (38 / 64),
          (ω (x, t) ^ 2 + ∑ j : Fin 3, G j x ^ 2 +
            ∑ j : Fin 3, ∑ k : Fin 3, H j k x ^ 2) ≤
          Cslice * (|Kw| + |K1| + |K2| + 1) := by
  obtain ⟨Ch, hCh, hsup⟩ := vorticity_heatSup_bm (r := 42 / 64) (R := 43 / 64) (κ := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, hsob⟩ := vorticity_sobolev_slice (r := 38 / 64) (R := 42 / 64)
    (by norm_num) (by norm_num)
  set A : ℝ := Ch * (|Kw| + |K1| + |K2|) + 1 with hAdef
  have hA : 0 ≤ A := by positivity
  refine ⟨Real.sqrt (Cs * (13 * A)), 13 * (Ch + 1), Real.sqrt_nonneg _, by positivity, ?_⟩
  intro x₀ a t₀ w g Fw h Fg Fh hat hta hw hg hh hFw hFg hFh hdw hdg hheatw hheatg hheath
    hKw hK1 hK2
  set W := (vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀ : Set (Vec3 × ℝ)) with hWdef
  have hWo : IsOpen W := vorticityBox_isOpen x₀ _ a t₀
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ _ _ (Metric.isBounded_Ioo a t₀)
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → IntegrableOn f W :=
    fun f hf => hf.integrable (by norm_num)
  have hloc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) := fun f hf =>
    ((integrable_indicator_iff hWm).2 (hint f hf)).locallyIntegrable
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii (show (0 : ℝ) < 1 / 768 by norm_num)
  set bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ :=
    fun f n => vorticityBackMollify W f (ε n) (hεpos n) with hbmdef
  let heatControl : VorticityContinuityExportHeatControl x₀ t₀ a Ch W bm := {
    squareBound := by
      intro q F hq hF hweak
      simpa [bm, W, vorticityContinuityExportHeatWeak] using
        (hsup x₀ a t₀ q F hat' hta hq hF hweak ε hεpos hεlim).1
    pairCauchy := by
      intro q F hq hF hweak δ hδ
      simpa [bm, W, vorticityContinuityExportHeatWeak] using
        (hsup x₀ a t₀ q F hat' hta hq hF hweak ε hεpos hεlim).2 δ hδ
  }
  have hbmS : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      ContDiff ℝ (⊤ : ℕ∞) (bm f n) := fun f hf n =>
    vorticityBackMollify_contDiff (hεpos n) (hloc f hf)
  have hc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      Continuous (bm f n) := fun f hf n => (hbmS f hf n).continuous
  have hball : ∀ n, ∀ z ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀,
      Metric.closedBall (z - vorticityBackShift (ε n)) (ε n) ⊆ W := fun n z hz =>
    vorticityBackBall_subset (hεpos n) (by have := hεle n; linarith only [this])
      (by have := hεle n; linarith only [this]) hz
  have r1 : ∀ n, ∀ z ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀, ∀ j,
      spatialPartial (bm w n) j z = bm (g j) n z := fun n z hz j =>
    vorticityBackMollify_spatialPartial_of_weak hWo (hint _ hw) (hdw j) (hεpos n) (hball n z hz)
  have r2 : ∀ n, ∀ z ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀, ∀ m k,
      spatialPartial (bm (g m) n) k z = bm (h m k) n z := fun n z hz m k =>
    vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hg m)) (hdg m k) (hεpos n)
      (hball n z hz)
  have hsl : ∀ f : Vec3 × ℝ → ℝ, Continuous f → ∀ t : ℝ, Continuous (fun x : Vec3 => f (x, t)) :=
    fun f hf t => hf.comp (continuous_id.prodMk continuous_const)
  have hib : ∀ f : Vec3 → ℝ, Continuous f → IntegrableOn f (vec3Ball x₀ (42 / 64)) :=
    fun f hf => vorticityHeatSmooth_integrableOn_ball hf x₀ _
  -- the embedding at a fixed time
  have key := vorticityContinuityExport_sliceSobolevBound x₀ Cs
  have hreg : ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ y ∈ vec3Ball x₀ (42 / 64),
      (y, t) ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀ := fun t ht y hy =>
    ⟨hy, by linarith only [ht.1], ht.2⟩
  have hat' : a + 1 / 64 < t₀ := hat
  -- Uniform mollification controls transfer the stage bounds and Cauchy estimates.
  obtain ⟨hboundW, hboundG, hboundH, hpairW, hpairG, hpairH⟩ :=
    vorticityContinuityExport_controlledMollificationIntegrals x₀ a t₀ Ch Kw K1 K2 hCh
      bm heatControl w g h Fw Fg Fh hw hg hh hFw hFg hFh hheatw hheatg hheath hKw hK1 hK2
  have hbd : ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x,
      vec3EuclideanNorm (x - x₀) ≤ 38 / 64 → bm w n (x, t) ^ 2 ≤ Cs * (13 * A) := by
    filter_upwards [hboundW, hboundG, hboundH] with n h1 h2 h3 t ht x hx
    exact key (bm w n) (fun j => bm (g j) n) (fun j k => bm (h j k) n) t A (hbmS _ hw n)
      (fun j => hbmS _ (hg j) n) (fun j k => hc _ (hh j k) n)
      (fun y hy j => r1 n _ (hreg t ht y hy) j) (fun y hy j k => r2 n _ (hreg t ht y hy) j k)
      (by simpa [A] using h1 t ht) (fun j => by simpa [A] using h2 j t ht)
      (fun j k => by simpa [A] using h3 j k t ht) x hx
  -- uniform Cauchy property of the approximations
  have hcauchy : ∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)),
      ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x, vec3EuclideanNorm (x - x₀) ≤ 38 / 64 →
        (bm w p.1 (x, t) - bm w p.2 (x, t)) ^ 2 ≤ Cs * (13 * δ) := by
    intro δ hδ
    have cw := hpairW δ hδ
    have cg := hpairG δ hδ
    have ch := hpairH δ hδ
    filter_upwards [cw, cg, ch] with p hp1 hp2 hp3 t ht x hx
    exact key (fun y => bm w p.1 y - bm w p.2 y) (fun j y => bm (g j) p.1 y - bm (g j) p.2 y)
      (fun j k y => bm (h j k) p.1 y - bm (h j k) p.2 y) t δ
      ((hbmS _ hw _).sub (hbmS _ hw _)) (fun j => (hbmS _ (hg j) _).sub (hbmS _ (hg j) _))
      (fun j k => (hc _ (hh j k) _).sub (hc _ (hh j k) _))
      (fun y hy j => (vorticity_spatialPartial_sub (hbmS _ hw _) (hbmS _ hw _) j (y, t)).trans
        (by rw [r1 p.1 _ (hreg t ht y hy) j, r1 p.2 _ (hreg t ht y hy) j]))
      (fun y hy j k => (vorticity_spatialPartial_sub (hbmS _ (hg j) _) (hbmS _ (hg j) _) k
        (y, t)).trans (by rw [r2 p.1 _ (hreg t ht y hy) j k, r2 p.2 _ (hreg t ht y hy) j k]))
      (hp1 t ht) (fun j => hp2 j t ht) (fun j k => hp3 j k t ht) x hx
  set K := ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀ :
    Set (Vec3 × ℝ)) with hKdef
  obtain ⟨ω, hωcontinuous, hωbounded, hlim, hTU⟩ :=
    vorticityContinuityExport_uniformCauchyLimit x₀ a t₀ Cs A (fun n => bm w n)
      (fun n => (hc _ hw n).continuous) hbd hcauchy
  refine ⟨ε, hεpos, ω, hωcontinuous, hωbounded, ?_, ?_, ?_⟩
  · set B := (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀ : Set (Vec3 × ℝ)) with hBdef
    have hBW : B ⊆ W := by
      rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
      refine ⟨vec3Ball_mono (by norm_num) hx, ?_, ht2⟩
      change a < t
      change a + 1 / 64 < t at ht1
      linarith only [ht1]
    have hBm : MeasurableSet B := (vorticityBox_isOpen x₀ _ _ t₀).measurableSet
    have hBb : Bornology.IsBounded B := hWb.subset hBW
    obtain ⟨φ, hφ, hae⟩ := vorticity_exists_subseq_ae (μ := volume.restrict B)
      (ι := Unit) (f := fun _ n => bm w n) (F := fun _ => w)
      (fun _ n => vorticity_memLp_two_of_continuous_bounded (hc _ hw n) hBb)
      (fun _ => hw.mono_measure (Measure.restrict_mono hBW le_rfl))
      (fun _ => vorticityBackMollify_tendsto_restrict hWm hBm hBW hw hεlim hεpos)
    filter_upwards [hae, ae_restrict_mem hBm] with z hz hzB
    have hzK : z ∈ K := ⟨show vec3EuclideanNorm (z.1 - x₀) ≤ 38 / 64 from le_of_lt hzB.1,
      le_of_lt hzB.2.1, le_of_lt hzB.2.2⟩
    exact tendsto_nhds_unique ((hlim z hzK).comp hφ.tendsto_atTop) (hz ())
  · simpa only [bm, hWdef] using hTU
  · intro t ht
    set Bs : Set Vec3 := vec3Ball x₀ (38 / 64) with hBsdef
    have hBsmeas : MeasurableSet Bs := (isOpen_vec3Ball x₀ _).measurableSet
    have hBs42 : Bs ⊆ vec3Ball x₀ (42 / 64) := by
      intro x hx
      have hx' : x ∈ vec3Ball x₀ (38 / 64) := by simpa only [Bs] using hx
      exact vec3Ball_mono (by norm_num) hx'
    have hsmem : ∀ (q : Vec3 × ℝ → ℝ) (hq : MemLp q 2 (volume.restrict W)) (n : ℕ),
        MemLp (fun x : Vec3 => bm q n (x, t)) 2 (volume.restrict Bs) := by
      intro q hq n
      apply (memLp_two_iff_integrable_sq
        (hsl _ (hc q hq n) t).aestronglyMeasurable).2
      exact vorticityHeatSmooth_integrableOn_ball ((hsl _ (hc q hq n) t).pow 2) x₀ _
    set S : ℝ := |Kw| + |K1| + |K2| with hSdef
    have hS0 : 0 ≤ S := by positivity
    have hsliceLimit : ∀ (q : Vec3 × ℝ → ℝ) (F : Fin 3 → Vec3 × ℝ → ℝ),
        MemLp q 2 (volume.restrict W) →
        (∀ j, MemLp (F j) 2 (volume.restrict W)) →
        vorticityContinuityExportHeatWeak W q F →
        (∫ y in W, (q y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) ≤ S →
        ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
          Tendsto (fun n => eLpNorm (fun x : Vec3 => bm q n (x, t) - Q x) 2
            (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A := by
      intro q F hq hF hheat hbudget
      have henergy : Ch * (∫ y in W, (q y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) + 1 ≤ A := by
        calc
          _ ≤ Ch * S + 1 := add_le_add (mul_le_mul_of_nonneg_left hbudget hCh) le_rfl
          _ = A := by simp [A, S]
      exact vorticityContinuityExport_sliceMollificationLimit x₀ a t₀ t Ch A ht bm
        heatControl q F hq hF hheat henergy (fun n => hsmem q hq n)
        (fun n => (hsl _ (hc q hq n) t)) hBsmeas hBs42
    have hstageLimit : ∀ q F, MemLp q 2 (volume.restrict W) →
        (∀ j, MemLp (F j) 2 (volume.restrict W)) →
        vorticityContinuityExportHeatWeak W q F →
        (∫ y in W, (q y ^ 2 + ∑ j : Fin 3, F j y ^ 2)) ≤ |Kw| + |K1| + |K2| →
        ∃ Q : Vec3 → ℝ, MemLp Q 2 (volume.restrict Bs) ∧
          Tendsto (fun n => eLpNorm (fun x : Vec3 => bm q n (x, t) - Q x) 2
            (volume.restrict Bs)) atTop (𝓝 0) ∧ (∫ x in Bs, Q x ^ 2) ≤ A := by
      intro q F hq hF hheat hbudget
      apply hsliceLimit q F hq hF hheat
      simpa [S] using hbudget
    obtain ⟨hWlim, hGlim, hHlim⟩ :=
      vorticityContinuityExport_stageTimeSliceLimits x₀ t A Kw K1 K2 bm hstageLimit
        w g h Fw Fg Fh hw hg hh hFw hFg hFh hheatw hheatg hheath hKw hK1 hK2
    obtain ⟨Wslice, hWsliceMem, hWsliceConv, hWsliceBound⟩ := hWlim
    choose G hGmem hGconv hGbound using hGlim
    choose H hHmem hHconv hHbound using hHlim
    have hWae : Wslice =ᵐ[volume.restrict Bs] (fun x => ω (x, t)) :=
      vorticityContinuityExport_identifyTimeSliceLimit (fun n x => bm w n (x, t)) Wslice
        (fun x => ω (x, t)) hBsmeas (fun n => hsmem w hw n) hWsliceMem hWsliceConv
        (fun x hx => hlim (x, t) ⟨le_of_lt hx.1, ht.1, ht.2⟩)
    have hωmem : MemLp (fun x : Vec3 => ω (x, t)) 2 (volume.restrict Bs) :=
      MemLp.ae_eq hWae hWsliceMem
    have hωconv : Tendsto (fun n => eLpNorm (fun x : Vec3 => bm w n (x, t) - ω (x, t)) 2
        (volume.restrict Bs)) atTop (𝓝 0) := hWsliceConv.congr fun n => by
      apply eLpNorm_congr_ae
      filter_upwards [hWae] with x hx
      simp only [hx]
    have hωboundSlice : (∫ x in Bs, ω (x, t) ^ 2) ≤ A := by
      have heq : (∫ x in Bs, ω (x, t) ^ 2) = ∫ x in Bs, Wslice x ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hWae, ae_restrict_mem hBsmeas] with x hx hxB
        rw [hx]
      exact heq.trans_le hWsliceBound
    have hlimitData := vorticityContinuityExport_limitSliceDerivatives Bs (fun x => ω (x, t))
      (fun n x => bm w n (x, t)) (fun j n x => bm (g j) n (x, t))
      (fun j k n x => bm (h j k) n (x, t)) G H A hBsmeas
      (fun n => (hbmS _ hw n).comp (contDiff_id.prodMk contDiff_const))
      (fun j n => (hbmS _ (hg j) n).comp (contDiff_id.prodMk contDiff_const))
      (fun n => hsmem w hw n) (fun j n => hsmem (g j) (hg j) n)
      (fun j k n => hsmem (h j k) (hh j k) n) hωmem hGmem hHmem hωconv hGconv hHconv
      (fun n x hx j => by
        calc
          spatialDeriv (fun y : Vec3 => bm w n (y, t)) j x = spatialPartial (bm w n) j (x, t) := rfl
          _ = bm (g j) n (x, t) := r1 n (x, t) (hreg t ht x (hBs42 hx)) j)
      (fun n x hx j k => by
        calc
          spatialDeriv (fun y : Vec3 => bm (g j) n (y, t)) k x =
              spatialPartial (bm (g j) n) k (x, t) := rfl
          _ = bm (h j k) n (x, t) := r2 n (x, t) (hreg t ht x (hBs42 hx)) j k)
      hωboundSlice hGbound hHbound
    refine ⟨G, H, hlimitData.1, hlimitData.2.1, ?_⟩
    dsimp [A, S]
    nlinarith only [hlimitData.2.2, hCh, hS0]

end ESS
