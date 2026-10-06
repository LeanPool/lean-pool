/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityFinalBound

/-!
# The continuous representative of the vorticity

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

/-- A continuous bounded representative on the closed box, from heat equations for the field and
its first and second spatial weak derivatives. -/
theorem vorticity_continuousRep (Kw K1 K2 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (w : Vec3 × ℝ → ℝ)
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
    ∃ ω : Vec3 × ℝ → ℝ,
      ContinuousOn ω ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀) ∧
      (∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀ :
        Set (Vec3 × ℝ)), |ω z| ≤ C) ∧
      ω =ᵐ[volume.restrict (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀)] w := by
  obtain ⟨Ch, hCh, hsup⟩ := vorticity_heatSup_bm (r := 42 / 64) (R := 43 / 64) (κ := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cs, hCs, hsob⟩ := vorticity_sobolev_slice (r := 38 / 64) (R := 42 / 64)
    (by norm_num) (by norm_num)
  set A : ℝ := Ch * (|Kw| + |K1| + |K2|) + 1 with hAdef
  have hA : 0 ≤ A := by positivity
  refine ⟨Real.sqrt (Cs * (13 * A)), Real.sqrt_nonneg _, ?_⟩
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
  have key : ∀ (f : Vec3 × ℝ → ℝ) (gg : Fin 3 → Vec3 × ℝ → ℝ)
      (hh : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (t B : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (gg j)) →
      (∀ j k, Continuous (hh j k)) →
      (∀ x ∈ vec3Ball x₀ (42 / 64), ∀ j, spatialPartial f j (x, t) = gg j (x, t)) →
      (∀ x ∈ vec3Ball x₀ (42 / 64), ∀ j k, spatialPartial (gg j) k (x, t) = hh j k (x, t)) →
      ∫ x in vec3Ball x₀ (42 / 64), f (x, t) ^ 2 ≤ B →
      (∀ j, ∫ x in vec3Ball x₀ (42 / 64), gg j (x, t) ^ 2 ≤ B) →
      (∀ j k, ∫ x in vec3Ball x₀ (42 / 64), hh j k (x, t) ^ 2 ≤ B) →
      ∀ x, vec3EuclideanNorm (x - x₀) ≤ 38 / 64 → f (x, t) ^ 2 ≤ Cs * (13 * B) := by
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
  have hreg : ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ y ∈ vec3Ball x₀ (42 / 64),
      (y, t) ∈ vec3Ball x₀ (42 / 64) ×ˢ Ioc (a + 1 / 128) t₀ := fun t ht y hy =>
    ⟨hy, by linarith only [ht.1], ht.2⟩
  have hat' : a + 1 / 64 < t₀ := hat
  -- uniform bounds of the approximations
  have hA1 : ∀ X : ℝ, X ≤ |Kw| + |K1| + |K2| → Ch * X + 1 ≤ A := fun X hX => by
    linarith only [mul_le_mul_of_nonneg_left hX hCh, hAdef]
  have habs := abs_nonneg Kw
  have habs1 := abs_nonneg K1
  have habs2 := abs_nonneg K2
  have hbd : ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x,
      vec3EuclideanNorm (x - x₀) ≤ 38 / 64 → bm w n (x, t) ^ 2 ≤ Cs * (13 * A) := by
    have bw := (hsup x₀ a t₀ w Fw hat' hta hw hFw hheatw ε hεpos hεlim).1
    have bg : ∀ᶠ n in atTop, ∀ m : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
        ∫ x in vec3Ball x₀ (42 / 64), bm (g m) n (x, t) ^ 2 ≤ A := by
      rw [eventually_all]
      intro m
      filter_upwards [(hsup x₀ a t₀ (g m) (Fg m) hat' hta (hg m) (hFg m) (hheatg m) ε hεpos
        hεlim).1] with n hn t ht
      exact (hn t ht).trans (hA1 _ (by linarith only [hK1 m, le_abs_self K1, habs, habs2]))
    have bh : ∀ᶠ n in atTop, ∀ m k : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
        ∫ x in vec3Ball x₀ (42 / 64), bm (h m k) n (x, t) ^ 2 ≤ A := by
      rw [eventually_all]
      intro m
      rw [eventually_all]
      intro k
      filter_upwards [(hsup x₀ a t₀ (h m k) (Fh m k) hat' hta (hh m k) (hFh m k) (hheath m k) ε
        hεpos hεlim).1] with n hn t ht
      exact (hn t ht).trans (hA1 _ (by linarith only [hK2 m k, le_abs_self K2, habs, habs1]))
    filter_upwards [bw, bg, bh] with n h1 h2 h3 t ht x hx
    exact key (bm w n) (fun j => bm (g j) n) (fun j k => bm (h j k) n) t A (hbmS _ hw n)
      (fun j => hbmS _ (hg j) n) (fun j k => hc _ (hh j k) n)
      (fun y hy j => r1 n _ (hreg t ht y hy) j) (fun y hy j k => r2 n _ (hreg t ht y hy) j k)
      ((h1 t ht).trans (hA1 _ (by linarith only [hKw, le_abs_self Kw, habs1, habs2])))
      (fun j => h2 j t ht) (fun j k => h3 j k t ht) x hx
  -- uniform Cauchy property of the approximations
  have hcauchy : ∀ δ : ℝ, 0 < δ → ∀ᶠ p in (atTop : Filter (ℕ × ℕ)),
      ∀ t ∈ Icc (a + 1 / 64) t₀, ∀ x, vec3EuclideanNorm (x - x₀) ≤ 38 / 64 →
        (bm w p.1 (x, t) - bm w p.2 (x, t)) ^ 2 ≤ Cs * (13 * δ) := by
    intro δ hδ
    have cw := (hsup x₀ a t₀ w Fw hat' hta hw hFw hheatw ε hεpos hεlim).2 δ hδ
    have cg : ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ∀ m : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
        ∫ x in vec3Ball x₀ (42 / 64), (bm (g m) p.1 (x, t) - bm (g m) p.2 (x, t)) ^ 2 ≤ δ := by
      rw [eventually_all]
      intro m
      exact (hsup x₀ a t₀ (g m) (Fg m) hat' hta (hg m) (hFg m) (hheatg m) ε hεpos hεlim).2 δ hδ
    have ch : ∀ᶠ p in (atTop : Filter (ℕ × ℕ)), ∀ m k : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
        ∫ x in vec3Ball x₀ (42 / 64),
          (bm (h m k) p.1 (x, t) - bm (h m k) p.2 (x, t)) ^ 2 ≤ δ := by
      rw [eventually_all]
      intro m
      rw [eventually_all]
      intro k
      exact (hsup x₀ a t₀ (h m k) (Fh m k) hat' hta (hh m k) (hFh m k) (hheath m k) ε hεpos
        hεlim).2 δ hδ
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
  have hUC : UniformCauchySeqOn (fun n => bm w n) atTop K := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro η hη
    have hne : (13 * Cs + 1) ≠ 0 := by positivity
    have hδ : 0 < η ^ 2 / (2 * (13 * Cs + 1)) := by positivity
    obtain ⟨⟨N1, N2⟩, hN⟩ := eventually_atTop.1 (hcauchy _ hδ)
    refine ⟨max N1 N2, fun m hm n hn z hz => ?_⟩
    obtain ⟨x, t⟩ := z
    have hb := hN (m, n) ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hn⟩ t hz.2
      x hz.1
    have e1 : (13 * Cs + 1) * (η ^ 2 / (2 * (13 * Cs + 1))) = η ^ 2 / 2 := by
      rw [mul_div_assoc', div_eq_div_iff (by positivity) (by norm_num)]
      ring
    have e2 : (13 * Cs + 1) * (η ^ 2 / (2 * (13 * Cs + 1))) =
        Cs * (13 * (η ^ 2 / (2 * (13 * Cs + 1)))) + η ^ 2 / (2 * (13 * Cs + 1)) := by ring
    have hη2 : 0 < η ^ 2 := by positivity
    rw [Real.dist_eq]
    exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hb (by linarith only [e1, e2, hδ, hη2])) hη.le
  have hlim : ∀ z ∈ K, Tendsto (fun n => bm w n z) atTop
      (𝓝 (limUnder atTop (fun n => bm w n z))) := fun z hz => (hUC.cauchySeq hz).tendsto_limUnder
  set ω : Vec3 × ℝ → ℝ := fun z => limUnder atTop (fun n => bm w n z) with hωdef
  have hTU : TendstoUniformlyOn (fun n => bm w n) ω atTop K :=
    hUC.tendstoUniformlyOn_of_tendsto hlim
  refine ⟨ω, hTU.continuousOn (Frequently.of_forall fun n => (hc _ hw n).continuousOn), ?_, ?_⟩
  · rintro ⟨x, t⟩ hz
    have hsq := ((continuous_pow 2).tendsto _).comp (hlim _ hz)
    exact Real.abs_le_sqrt (le_of_tendsto hsq (hbd.mono fun n hn => hn t hz.2 x hz.1))
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

end ESS
