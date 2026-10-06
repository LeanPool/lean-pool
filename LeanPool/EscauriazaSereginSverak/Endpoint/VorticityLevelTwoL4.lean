/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityFatou
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLevelOne
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityGNSmooth

/-!
# The fourth-power bound for the velocity gradient

A bounded velocity whose gradient and second derivatives are square integrable has a gradient in
`L⁴` on a smaller box, with the bound of `lem:vorticity-products` (the `H²` product estimate): the
smooth interpolation inequality applied at every time to backward mollifications, integrated in
time, and passed to the limit by Fatou's lemma.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Coordinate derivatives of functions agreeing on an open set agree there. -/
theorem vorticity_spatialDeriv_congr_on {f g : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U)
    (hfg : ∀ x ∈ U, f x = g x) {x : Vec3} (hx : x ∈ U) (j : Fin 3) :
    spatialDeriv f j x = spatialDeriv g j x := by
  have hev : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hU.mem_nhds hx) hfg
  unfold spatialDeriv
  rw [hev.fderiv_eq]

/-- An almost-everywhere bound on a set bounds the zero extension. -/
theorem vorticity_indicator_bound {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {f : Vec3 × ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ᵐ z ∂(volume.restrict W), |f z| ≤ M) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)), |W.indicator f z| ≤ M := by
  rw [ae_restrict_iff' hW] at hf
  filter_upwards [hf] with z hz
  by_cases hzW : z ∈ W
  · rw [Set.indicator_of_mem hzW]
    exact hz hzW
  · rw [Set.indicator_of_notMem hzW, abs_zero]
    exact hM

/-- The square of a sum of three nonnegative terms is at most three times the sum of squares. -/
theorem vorticity_sq_sum_three_le (A : Fin 3 → ℝ) :
    (∑ i : Fin 3, A i) ^ 2 ≤ 3 * ∑ i : Fin 3, A i ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (A 0 - A 1), sq_nonneg (A 1 - A 2), sq_nonneg (A 0 - A 2)]

/-- The fourth-power bound for the velocity gradient on a smaller box (the `H²` product estimate
of `lem:vorticity-products`, localized). -/
theorem vorticityLevelTwo_L4 (M K₀ K₂ : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (D2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀))) →
    (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀)), ∀ i, |U i z| ≤ M) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀))) →
    ∫ z in vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤ K₀ →
    (∀ i j k, MemLp (D2 i j k) 2 (volume.restrict (vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀))) →
    ∫ z in vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀,
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k z ^ 2 ≤ K₂ →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀, U i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀, G i j y * ψ y) →
    (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀, G i j y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀, D2 i j k y * ψ y) →
    Integrable (fun z => (∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2) ^ 2)
        (volume.restrict (vec3Ball x₀ (13 / 16) ×ˢ Ioo (a + 1 / 16) t₀)) ∧
      ∫ z in vec3Ball x₀ (13 / 16) ×ˢ Ioo (a + 1 / 16) t₀,
        (∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2) ^ 2 ≤ K := by
  obtain ⟨Cg, hCg, hgn⟩ := vorticityGNSmooth_local (r := 13 / 16) (R := 27 / 32)
    (by norm_num) (by norm_num)
  refine ⟨3 * (Cg * M ^ 2 * (|K₂| + |K₀|)) + 1, by positivity, ?_⟩
  intro x₀ a t₀ U G D2 hU hUb hG hGb hD2 hD2b hdU hdG
  set W := (vec3Ball x₀ (14 / 16) ×ˢ Ioo a t₀ : Set (Vec3 × ℝ)) with hWdef
  set W' := (vec3Ball x₀ (13 / 16) ×ˢ Ioo (a + 1 / 16) t₀ : Set (Vec3 × ℝ)) with hW'def
  set Wr := (vec3Ball x₀ (27 / 32) ×ˢ Ioo (a + 1 / 16) t₀ : Set (Vec3 × ℝ)) with hWrdef
  have hWo : IsOpen W := vorticityBox_isOpen x₀ _ a t₀
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ _ _ (Metric.isBounded_Ioo a t₀)
  have hW'W : W' ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨show vec3EuclideanNorm (x - x₀) < 14 / 16 from
      lt_trans (show vec3EuclideanNorm (x - x₀) < 13 / 16 from hx) (by norm_num), ?_, ht2⟩
    change a < t
    change a + 1 / 16 < t at ht1
    linarith only [ht1]
  have hWrW : Wr ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨show vec3EuclideanNorm (x - x₀) < 14 / 16 from
      lt_trans (show vec3EuclideanNorm (x - x₀) < 27 / 32 from hx) (by norm_num), ?_, ht2⟩
    change a < t
    change a + 1 / 16 < t at ht1
    linarith only [ht1]
  have hW'm : MeasurableSet W' := (vorticityBox_isOpen x₀ _ _ t₀).measurableSet
  have hW'b : Bornology.IsBounded W' := hWb.subset hW'W
  have hWrb : Bornology.IsBounded Wr := hWb.subset hWrW
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → IntegrableOn f W :=
    fun f hf => hf.integrable (by norm_num)
  have hloc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) := fun f hf =>
    ((integrable_indicator_iff hWm).2 (hint f hf)).locallyIntegrable
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii (show (0 : ℝ) < 1 / 192 by norm_num)
  set Un : ℕ → Fin 3 → Vec3 × ℝ → ℝ := fun n i => vorticityBackMollify W (U i) (ε n) (hεpos n)
  set Gn : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n i j => vorticityBackMollify W (G i j) (ε n) (hεpos n)
  set D2n : ℕ → Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    fun n i j k => vorticityBackMollify W (D2 i j k) (ε n) (hεpos n)
  have hUn : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (Un n i) := fun n i =>
    vorticityBackMollify_contDiff (hεpos n) (hloc _ (hU i))
  have hGn : ∀ n i j, ContDiff ℝ (⊤ : ℕ∞) (Gn n i j) := fun n i j =>
    vorticityBackMollify_contDiff (hεpos n) (hloc _ (hG i j))
  have hD2n : ∀ n i j k, ContDiff ℝ (⊤ : ℕ∞) (D2n n i j k) := fun n i j k =>
    vorticityBackMollify_contDiff (hεpos n) (hloc _ (hD2 i j k))
  -- the region where the commutation holds
  have hball : ∀ n, ∀ z ∈ vec3Ball x₀ (27 / 32) ×ˢ Ioc (a + 1 / 32) t₀,
      Metric.closedBall (z - vorticityBackShift (ε n)) (ε n) ⊆ W := fun n z hz =>
    vorticityBackBall_subset (hεpos n) (by have := hεle n; linarith only [this])
      (by have := hεle n; linarith only [this]) hz
  have hcU : ∀ n i j, ∀ z ∈ vec3Ball x₀ (27 / 32) ×ˢ Ioc (a + 1 / 32) t₀,
      spatialPartial (Un n i) j z = Gn n i j z := fun n i j z hz =>
    vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hU i)) (hdU i j) (hεpos n)
      (hball n z hz)
  have hcG : ∀ n i j k, ∀ z ∈ vec3Ball x₀ (27 / 32) ×ˢ Ioc (a + 1 / 32) t₀,
      spatialPartial (Gn n i j) k z = D2n n i j k z := fun n i j k z hz =>
    vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hG i j)) (hdG i j k) (hεpos n)
      (hball n z hz)
  have hbd : ∀ n i z, |Un n i z| ≤ M := fun n i z =>
    vorticityBackMollify_abs_le (hεpos n)
      (vorticity_indicator_bound hWm hM (by filter_upwards [hUb] with z hz using hz i)) z
  -- the smooth interpolation inequality at each time
  have hpertime : ∀ n i, ∀ t ∈ Ioo (a + 1 / 16) t₀,
      ∫ x in vec3Ball x₀ (13 / 16), (∑ j : Fin 3, Gn n i j (x, t) ^ 2) ^ 2 ≤
        ∫ x in vec3Ball x₀ (27 / 32), Cg * M ^ 2 * (∑ j : Fin 3, ∑ k : Fin 3,
          D2n n i j k (x, t) ^ 2 + ∑ j : Fin 3, Gn n i j (x, t) ^ 2) := by
    intro n i t ht
    set f : Vec3 → ℝ := fun x => Un n i (x, t) with hfdef
    have hf : ContDiff ℝ (⊤ : ℕ∞) f := (hUn n i).comp (contDiff_id.prodMk contDiff_const)
    have hreg : ∀ x ∈ vec3Ball x₀ (27 / 32),
        (x, t) ∈ vec3Ball x₀ (27 / 32) ×ˢ Ioc (a + 1 / 32) t₀ := fun x hx =>
      ⟨hx, by linarith only [ht.1], le_of_lt ht.2⟩
    have d1 : ∀ j, ∀ x ∈ vec3Ball x₀ (27 / 32), spatialDeriv f j x = Gn n i j (x, t) :=
      fun j x hx => hcU n i j (x, t) (hreg x hx)
    have d2 : ∀ j k, ∀ x ∈ vec3Ball x₀ (27 / 32),
        spatialDeriv (spatialDeriv f j) k x = D2n n i j k (x, t) := by
      intro j k x hx
      rw [vorticity_spatialDeriv_congr_on (isOpen_vec3Ball x₀ _) (d1 j) hx k]
      exact hcG n i j k (x, t) (hreg x hx)
    have h := hgn x₀ f M hf hM (fun x hx => hbd n i (x, t))
    have hsub : vec3Ball x₀ (13 / 16) ⊆ vec3Ball x₀ (27 / 32) := vec3Ball_mono (by norm_num)
    have eL : ∫ x in vec3Ball x₀ (13 / 16), (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2 =
        ∫ x in vec3Ball x₀ (13 / 16), (∑ j : Fin 3, Gn n i j (x, t) ^ 2) ^ 2 :=
      setIntegral_congr_fun (isOpen_vec3Ball x₀ _).measurableSet fun x hx => by
        simp only [d1 _ x (hsub hx)]
    have eR : ∫ x in vec3Ball x₀ (27 / 32), (∑ j : Fin 3, ∑ k : Fin 3,
          spatialDeriv (spatialDeriv f j) k x ^ 2 + ∑ j : Fin 3, spatialDeriv f j x ^ 2) =
        ∫ x in vec3Ball x₀ (27 / 32), (∑ j : Fin 3, ∑ k : Fin 3,
          D2n n i j k (x, t) ^ 2 + ∑ j : Fin 3, Gn n i j (x, t) ^ 2) :=
      setIntegral_congr_fun (isOpen_vec3Ball x₀ _).measurableSet fun x hx => by
        simp only [d1 _ x hx, d2 _ _ x hx]
    rw [eL, eR] at h
    rw [integral_const_mul]
    exact h
  have hcont : ∀ (h : Vec3 × ℝ → ℝ) (S : Set (Vec3 × ℝ)), Continuous h →
      Bornology.IsBounded S → IntegrableOn h S := fun h S hh hS =>
    vorticity_integrableOn_of_continuous_bounded hh hS
  have hRn : ∀ n i, Continuous (fun z => ∑ j : Fin 3, ∑ k : Fin 3, D2n n i j k z ^ 2 +
      ∑ j : Fin 3, Gn n i j z ^ 2) := fun n i => by
    refine Continuous.add ?_ ?_
    · exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        (hD2n n i j k).continuous.pow 2
    · exact continuous_finsetSum _ fun j _ => (hGn n i j).continuous.pow 2
  have hLn : ∀ n i, Continuous (fun z => (∑ j : Fin 3, Gn n i j z ^ 2) ^ 2) := fun n i =>
    (continuous_finsetSum _ fun j _ => (hGn n i j).continuous.pow 2).pow 2
  -- integrate over time
  have hstepn : ∀ n i, ∫ z in W', (∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 ≤
      Cg * M ^ 2 * ∫ z in W, (∑ j : Fin 3, ∑ k : Fin 3, D2n n i j k z ^ 2 +
        ∑ j : Fin 3, Gn n i j z ^ 2) := by
    intro n i
    have h1 := vorticity_setIntegral_prod_time_mono measurableSet_Ioo
      (hcont _ W' (hLn n i) hW'b) (hcont _ Wr ((continuous_const.mul (hRn n i))) hWrb)
      (hpertime n i)
    have h2 : ∫ z in Wr, Cg * M ^ 2 * (∑ j : Fin 3, ∑ k : Fin 3, D2n n i j k z ^ 2 +
        ∑ j : Fin 3, Gn n i j z ^ 2) = Cg * M ^ 2 * ∫ z in Wr, (∑ j : Fin 3, ∑ k : Fin 3,
          D2n n i j k z ^ 2 + ∑ j : Fin 3, Gn n i j z ^ 2) := integral_const_mul _ _
    have h3 : ∫ z in Wr, (∑ j : Fin 3, ∑ k : Fin 3, D2n n i j k z ^ 2 +
        ∑ j : Fin 3, Gn n i j z ^ 2) ≤ ∫ z in W, (∑ j : Fin 3, ∑ k : Fin 3,
          D2n n i j k z ^ 2 + ∑ j : Fin 3, Gn n i j z ^ 2) :=
      setIntegral_mono_set (hcont _ W (hRn n i) hWb)
        (Eventually.of_forall fun z => by positivity) (Eventually.of_forall hWrW)
    calc
      _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have htot : ∀ n, ∫ z in W', (∑ i : Fin 3, ∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 ≤
      3 * (Cg * M ^ 2 * ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, D2n n i j k z ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, Gn n i j z ^ 2)) := by
    intro n
    have hGi : ∀ i j, IntegrableOn (fun z => Gn n i j z ^ 2) W := fun i j =>
      hcont _ W ((hGn n i j).continuous.pow 2) hWb
    have hDi : ∀ i j k, IntegrableOn (fun z => D2n n i j k z ^ 2) W := fun i j k =>
      hcont _ W ((hD2n n i j k).continuous.pow 2) hWb
    have hA : IntegrableOn (fun z => (∑ i : Fin 3, ∑ j : Fin 3, Gn n i j z ^ 2) ^ 2) W' :=
      hcont _ W' ((continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => (hGn n i j).continuous.pow 2).pow 2) hW'b
    have hB : IntegrableOn (fun z => 3 * ∑ i : Fin 3, (∑ j : Fin 3, Gn n i j z ^ 2) ^ 2) W' :=
      (integrable_finsetSum _ fun i _ => hcont _ W' (hLn n i) hW'b).const_mul 3
    have hAB : ∫ z in W', (∑ i : Fin 3, ∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 ≤
        ∫ z in W', 3 * ∑ i : Fin 3, (∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 :=
      integral_mono hA hB fun z => vorticity_sq_sum_three_le (fun i => ∑ j : Fin 3, Gn n i j z ^ 2)
    calc
      ∫ z in W', (∑ i : Fin 3, ∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 ≤
          ∫ z in W', 3 * ∑ i : Fin 3, (∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 := hAB
      _ = 3 * ∑ i : Fin 3, ∫ z in W', (∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hcont _ W' (hLn n i) hW'b]
      _ ≤ 3 * ∑ i : Fin 3, Cg * M ^ 2 * ∫ z in W, (∑ j : Fin 3, ∑ k : Fin 3,
          D2n n i j k z ^ 2 + ∑ j : Fin 3, Gn n i j z ^ 2) := by
        gcongr with i
        exact hstepn n i
      _ = _ := by
        congr 1
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_add (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
            hDi i j k) (integrable_finsetSum _ fun j _ => hGi i j),
          integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hDi i j k,
          integral_finsetSum _ fun j _ => hGi i j]
        rw [Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hDi i j k]
  -- the limit of the right sides
  have hWsub : W ⊆ W := subset_rfl
  have hconvW : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      Tendsto (fun n => eLpNorm (vorticityBackMollify W f (ε n) (hεpos n) - f) 2
        (volume.restrict W)) atTop (𝓝 0) := fun f hf =>
    vorticityBackMollify_tendsto_restrict hWm hWm hWsub hf hεlim hεpos
  have hmemW : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      MemLp (vorticityBackMollify W f (ε n) (hεpos n)) 2 (volume.restrict W) := fun f hf n =>
    vorticity_memLp_two_of_continuous_bounded
      (vorticityBackMollify_contDiff (hεpos n) (hloc f hf)).continuous hWb
  have hlimR : Tendsto (fun n => 3 * (Cg * M ^ 2 *
      ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, D2n n i j k z ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, Gn n i j z ^ 2))) atTop
      (𝓝 (3 * (Cg * M ^ 2 *
        ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, D2 i j k z ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, G i j z ^ 2)))) := by
    refine ((Tendsto.add ?_ ?_).const_mul _).const_mul _
    · exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        tendsto_finsetSum _ fun k _ => vorticity_tendsto_integral_sq
          (hmemW _ (hD2 i j k)) (hD2 i j k) (hconvW _ (hD2 i j k))
    · exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        vorticity_tendsto_integral_sq (hmemW _ (hG i j)) (hG i j) (hconvW _ (hG i j))
  have hsq : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      IntegrableOn (fun z => f z ^ 2) W := fun f hf =>
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hvalD : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, D2 i j k z ^ 2) ≤ |K₂| := by
    have e : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, D2 i j k z ^ 2) =
        ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k z ^ 2 := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => hsq _ (hD2 i j k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hsq _ (hD2 i j k)]
      exact Finset.sum_congr rfl fun j _ =>
        (integral_finsetSum _ fun k _ => hsq _ (hD2 i j k)).symm
    rw [e]
    exact hD2b.trans (le_abs_self _)
  have hvalG : (∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, G i j z ^ 2) ≤ |K₀| := by
    have e : (∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, G i j z ^ 2) =
        ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hsq _ (hG i j)]
      exact Finset.sum_congr rfl fun i _ =>
        (integral_finsetSum _ fun j _ => hsq _ (hG i j)).symm
    rw [e]
    exact hGb.trans (le_abs_self _)
  have hlimval : 3 * (Cg * M ^ 2 *
      ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, D2 i j k z ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, G i j z ^ 2)) <
      3 * (Cg * M ^ 2 * (|K₂| + |K₀|)) + 1 := by
    have h := add_le_add hvalD hvalG
    have hc : 0 ≤ Cg * M ^ 2 := by positivity
    nlinarith only [h, hc]
  have hev : ∀ᶠ n in atTop, ∫ z in W', (∑ i : Fin 3, ∑ j : Fin 3, Gn n i j z ^ 2) ^ 2 ≤
      3 * (Cg * M ^ 2 * (|K₂| + |K₀|)) + 1 := by
    filter_upwards [hlimR.eventually (gt_mem_nhds hlimval)] with n hn
    exact (htot n).trans (le_of_lt hn)
  -- Fatou
  have hW'W' : W' ⊆ W := hW'W
  exact vorticity_integral_le_of_L2_tendsto (μ := volume.restrict W') (ι := Fin 3 × Fin 3)
    (a := fun p n => Gn n p.1 p.2) (A := fun p => G p.1 p.2)
    (fun p n => vorticity_memLp_two_of_continuous_bounded (hGn n p.1 p.2).continuous hW'b)
    (fun p => (hG p.1 p.2).mono_measure (Measure.restrict_mono hW'W' le_rfl))
    (fun p => vorticityBackMollify_tendsto_restrict hWm hW'm hW'W' (hG p.1 p.2) hεlim hεpos)
    (H := fun v => (∑ i : Fin 3, ∑ j : Fin 3, v (i, j) ^ 2) ^ 2)
    (by fun_prop) (fun v => by positivity)
    (fun n => hcont _ W' ((continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => (hGn n i j).continuous.pow 2).pow 2) hW'b)
    hev

end ESS
