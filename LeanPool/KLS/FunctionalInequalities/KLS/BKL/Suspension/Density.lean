/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Law
public import LeanPool.KLS.FunctionalInequalities.Probability.Product
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments

/-!
# The density of the suspension law (BKL (109))

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28: for
`μ = e^{-V} dx / Z`, the joint law of `(S, X₁, …, X_N)` is the normalized tilted Lebesgue law of
`W_N(s, x) = Σ V(x_i) + β |σ s - N^{-1/2} Σ f(x_i)|` (`Suspension.potential`), for every `N` and
`n` (including `0`), assuming only measurable `V`, `f`, `β > 0` and integrable `e^{-V}`.

The argument: the product of the Lebesgue densities of `μ^{⊗N}` and the Laplace law, a measurable
nonlinear fibrewise shear `η ↦ (F_N(x) + η)/σ` (density multiplier `σ`, from `dη = σ ds`), a
volume-preserving coordinate equivalence onto `EuclideanSpace ℝ (Option (Fin N × Fin n))`, and
normalization of a positive density. The helpers are private to this boundary.

The finite-product integral identity is `Probability.lintegral_pi_prod_fin`.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities.Probability.Line

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-- **Push-forward under the fibrewise shear** `(a, η) ↦ (a, (F a + η)/σ)`: a density `w` on
`μ ⊗ ds` becomes `|σ| · w(a, σ s - F a)`, the inverse Jacobian of the shear. -/
private theorem map_density_shift_scale {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [SFinite μ] (F : A → ℝ) (hF : Measurable F) (σ : ℝ) (hσ : σ ≠ 0) (w : A × ℝ → ENNReal)
    (hw : Measurable w) :
    ((μ.prod volume).withDensity w).map (fun p => (p.1, (F p.1 + p.2) / σ)) =
      (μ.prod volume).withDensity (fun p => ENNReal.ofReal |σ| * w (p.1, σ * p.2 - F p.1)) := by
  let e : A × ℝ ≃ᵐ A × ℝ :=
    { toFun p := (p.1, (F p.1 + p.2) / σ)
      invFun p := (p.1, σ * p.2 - F p.1)
      left_inv
        p := by
        apply Prod.ext
        · rfl
        · dsimp
          field_simp
          ring
      right_inv
        p := by
        apply Prod.ext
        · rfl
        · dsimp
          field_simp
          ring
      measurable_toFun :=
        measurable_fst.prodMk (((hF.comp measurable_fst).add measurable_snd).div_const σ)
      measurable_invFun :=
        measurable_fst.prodMk
          ((measurable_const.mul measurable_snd).sub (hF.comp measurable_fst)) }
  have hshift :
    MeasurePreserving (fun p : A × ℝ => (p.1, F p.1 + p.2)) (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).skew_product ((hF.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun x => map_add_left_eq_self volume (F x))
  have hreal : (volume : Measure ℝ).map (fun x => x / σ) = ENNReal.ofReal |σ| • volume := by
    simpa only [inv_inv, mul_comm, div_eq_mul_inv] using
      (Real.map_volume_mul_left (inv_ne_zero hσ))
  have hscale :
    (μ.prod volume).map (fun p : A × ℝ => (p.1, p.2 / σ)) =
      ENNReal.ofReal |σ| • μ.prod volume := by
    change (μ.prod volume).map (Prod.map id (fun x => x / σ)) = _
    rw [←
      Measure.map_prod_map μ volume measurable_id
        (show Measurable (fun x : ℝ => x / σ) from measurable_id.div_const σ),
      Measure.map_id, hreal, Measure.prod_smul_right]
  have hbase : (μ.prod volume).map e = ENNReal.ofReal |σ| • μ.prod volume := by
    change
      (μ.prod volume).map
          ((fun p : A × ℝ => (p.1, p.2 / σ)) ∘ (fun p : A × ℝ => (p.1, F p.1 + p.2))) =
        _
    rw [←
      Measure.map_map (measurable_fst.prodMk (measurable_snd.div_const σ)) hshift.measurable,
      hshift.map_eq, hscale]
  change ((μ.prod volume).withDensity w).map e = _
  rw [Probability.map_withDensity_measurableEquiv e (μ.prod volume) w hw, hbase,
    withDensity_smul_measure, ←
    withDensity_smul (ENNReal.ofReal |σ|)
      (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable)]
  rfl

private theorem normalized_of_probability_density {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (W : A → ℝ) (hW : Measurable W) {C : ℝ} (hC : 0 < C)
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))))) :
    Integrable (fun x => Real.exp (W x)) μ ∧
      μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))) = μ.tilted W := by
  let := hprob
  have hmass : ∫⁻ x, ENNReal.ofReal (C * Real.exp (W x)) ∂μ = 1 := by
    have hm := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))))
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hm
  have hmeas : Measurable (fun x => C * Real.exp (W x)) := measurable_const.mul hW.exp
  have hnonneg : ∀ x, 0 ≤ C * Real.exp (W x) := fun x => mul_nonneg hC.le (Real.exp_pos _).le
  have hInt : Integrable (fun x => C * Real.exp (W x)) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal (hnonneg _)]
    rw [hmass]
    exact ENNReal.one_lt_top
  have hexp : Integrable (fun x => Real.exp (W x)) μ := by
    have ht := hInt.const_mul C⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using ht
  have ho : ENNReal.ofReal (∫ x, C * Real.exp (W x) ∂μ) = 1 :=
    (ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hnonneg)).trans hmass
  have hval : (∫ x, C * Real.exp (W x) ∂μ) = 1 := by
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hnonneg) zero_le_one).1
      (by simpa only [ENNReal.ofReal_one] using ho)
  have hnorm : C * (∫ x, Real.exp (W x) ∂μ) = 1 := by
    rw [← integral_const_mul C]
    exact hval
  have hz : (∫ x, Real.exp (W x) ∂μ) = C⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hC.ne').2 (by simpa only [mul_comm] using hnorm)
  refine ⟨hexp, ?_⟩
  unfold Measure.tilted
  congr 1
  funext x
  rw [hz, div_eq_mul_inv, inv_inv, mul_comm]

private theorem piWithDensityOfReal {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (ρ : E → ℝ) (hρ : Measurable ρ)
    (_hρnonneg : ∀ x, 0 ≤ ρ x) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ.withDensity (fun x => ENNReal.ofReal (ρ x))) =
      (Measure.pi (fun _ : Fin N => μ)).withDensity
        (fun x => ∏ i : Fin N, ENNReal.ofReal (ρ (x i))) := by
  classical
  let q : E → ENNReal := fun x => ENNReal.ofReal (ρ x)
  have hq : Measurable q := hρ.ennreal_ofReal
  apply Measure.pi_eq
  intro s hs
  have hrect : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  have hfactor (x : Fin N → E) :
      (Set.pi Set.univ s).indicator (fun x => ∏ i : Fin N, q (x i)) x =
        ∏ i : Fin N, (s i).indicator q (x i) := by
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Set.indicator_of_mem (hx i (Set.mem_univ i)) q).symm
    · rw [Set.indicator_of_notMem hx]
      symm
      have hnot : ¬ ∀ i : Fin N, x i ∈ s i := by
        intro hall
        exact hx (fun i _ => hall i)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi q)
  calc
    ((Measure.pi (fun _ : Fin N => μ)).withDensity
        (fun x => ∏ i : Fin N, ENNReal.ofReal (ρ (x i)))) (Set.pi Set.univ s) =
        ∫⁻ x in Set.pi Set.univ s, ∏ i : Fin N, q (x i)
          ∂(Measure.pi (fun _ : Fin N => μ)) := by
            exact withDensity_apply _ hrect
    _ = ∫⁻ x, (Set.pi Set.univ s).indicator (fun x => ∏ i : Fin N, q (x i)) x
          ∂(Measure.pi (fun _ : Fin N => μ)) := (lintegral_indicator hrect _).symm
    _ = ∫⁻ x, ∏ i : Fin N, (s i).indicator q (x i)
          ∂(Measure.pi (fun _ : Fin N => μ)) := lintegral_congr hfactor
    _ = ∏ i : Fin N, ∫⁻ x, (s i).indicator q x ∂μ :=
      Probability.lintegral_pi_prod_fin μ N (fun i => (s i).indicator q)
        (fun i => hq.indicator (hs i))
    _ = ∏ i : Fin N, (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) (s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [withDensity_apply _ (hs i)]
      exact lintegral_indicator (hs i) q

private theorem raw_uncurry_volume_preserving (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.uncurry : (ι → κ → ℝ) → (ι × κ → ℝ)) volume volume := by
  refine ⟨measurable_uncurry, ?_⟩
  change (Measure.pi fun _ : ι => (Measure.pi fun _ : κ => (volume : Measure ℝ))).map
    Function.uncurry = Measure.pi (fun _ : ι × κ => (volume : Measure ℝ))
  apply (Measure.pi_eq (μ := fun _ : ι × κ => (volume : Measure ℝ)) ?_).symm
  intro s hs
  have he : Function.uncurry ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i : ι => Set.pi Set.univ (fun j : κ => s (i, j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Function.uncurry, Prod.forall]
  rw [Measure.map_apply measurable_uncurry (MeasurableSet.univ_pi hs), he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

private theorem raw_option_volume_preserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
      volume volume := by
  refine ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm.measurable, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option ι => (volume : Measure ℝ))

private theorem raw_assembly_volume_preserving (N n : ℕ) :
    MeasurePreserving
      (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
        (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2 : JointSpace N n))
      volume volume := by
  let blockOfLp : (Fin N → EuclideanSpace ℝ (Fin n)) → (Fin N → Fin n → ℝ) := fun x i =>
    (x i).ofLp
  have hblock : MeasurePreserving blockOfLp volume volume :=
    volume_preserving_pi (fun _ : Fin N => PiLp.volume_preserving_ofLp (Fin n))
  have hflat : MeasurePreserving (Function.uncurry ∘ blockOfLp) volume volume :=
    (raw_uncurry_volume_preserving (Fin N) (Fin n)).comp hblock
  have hprod :
    MeasurePreserving (Prod.map (Function.uncurry ∘ blockOfLp) (id : ℝ → ℝ)) volume volume := by
    simpa only [← Measure.volume_eq_prod] using
      hflat.prod (MeasurePreserving.id (volume : Measure ℝ))
  have heq :
    (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
        (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2 : JointSpace N n)) =
      WithLp.toLp 2 ∘
        (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin N × Fin n) => ℝ)).symm ∘
          Prod.map (Function.uncurry ∘ blockOfLp) id := by
    funext q
    ext o
    cases o <;> rfl
  rw [heq]
  exact
    (PiLp.volume_preserving_toLp (Option (Fin N × Fin n))).comp
      ((raw_option_volume_preserving (Fin N × Fin n)).comp hprod)

private theorem raw_assembly_left_inverse (N n : ℕ)
    (q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) :
    (fun p : JointSpace N n =>
      (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none))
      (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2) = q := by
  rcases q with ⟨x, s⟩
  apply Prod.ext
  · funext i
    ext j
    rfl
  · rfl

private theorem raw_assembly_right_inverse (N n : ℕ) (p : JointSpace N n) :
    (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
          (WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2 : JointSpace N n))
        (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none) =
      p := by
  ext o
  cases o <;> rfl

private theorem raw_assembly_inverse_measurable (N n : ℕ) :
    Measurable (fun p : JointSpace N n =>
      (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none)) := by
  fun_prop

/-- Construct the actual measurable equivalence locally, ready for inverse-density transport. -/
private theorem exists_raw_assembly_equiv (N n : ℕ) :
    ∃ e : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) ≃ᵐ JointSpace N n,
      (∀ q, e q = WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2) ∧
      (∀ p, e.symm p =
        (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none)) ∧
      MeasurePreserving e volume volume := by
  let e : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) ≃ᵐ JointSpace N n :=
    { toEquiv :=
        { toFun := fun q => WithLp.toLp 2 fun o => Option.elim o q.2 fun ij => q.1 ij.1 ij.2
          invFun := fun p =>
            (fun i : Fin N => WithLp.toLp 2 fun j : Fin n => p (some (i, j)), p none)
          left_inv := raw_assembly_left_inverse N n
          right_inv := raw_assembly_right_inverse N n }
      measurable_toFun := (raw_assembly_volume_preserving N n).measurable
      measurable_invFun := raw_assembly_inverse_measurable N n }
  exact ⟨e, fun _ => rfl, fun _ => rfl, raw_assembly_volume_preserving N n⟩

private theorem joint_density_product {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β σ Z : ℝ}
    (hσ : 0 < σ) (hZ : 0 < Z)
    (s : ℝ) (x : Fin N → EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal |σ| *
      ((∏ i : Fin N, ENNReal.ofReal (Real.exp (-V (x i)) / Z)) *
        ENNReal.ofReal (laplaceDensity β (σ * s - copyStat f N x))) =
      ENNReal.ofReal ((σ * (β / 2) / Z ^ N) *
        Real.exp (-potential V f β σ N (s, x))) := by
  have hp : 0 ≤ ∏ i : Fin N, Real.exp (-V (x i)) / Z := by positivity
  rw [abs_of_pos hσ,
    ← ENNReal.ofReal_prod_of_nonneg
      (fun (i : Fin N) _ => div_nonneg (Real.exp_pos _).le hZ.le),
    ← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hσ.le]
  congr 1
  have he : (∏ i : Fin N, Real.exp (-V (x i))) =
      Real.exp (-(∑ i : Fin N, V (x i))) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, he]
  simp only [laplaceDensity, potential, copyStat, neg_add, Real.exp_add]
  ring

/-- **The density (109).** -/
theorem jointLaw_eq_tilted {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β : ℝ} (hβ : 0 < β)
    (hV : Measurable V) (hf : Measurable f) (hint : Integrable (fun x => Real.exp (-V x))) :
    jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
      (volume : Measure (JointSpace N n)).tilted fun p =>
        -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))) := by
  classical
  let Z : ℝ := ∫ x, Real.exp (-V x)
  let σ : ℝ := sigma β
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (fun x => -V x)
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-V x) / Z
  let H : (Fin N → EuclideanSpace ℝ (Fin n)) → ENNReal :=
    fun x => ∏ i : Fin N, ENNReal.ofReal (ρ (x i))
  let w : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) → ENNReal :=
    fun q => H q.1 * ENNReal.ofReal (laplaceDensity β q.2)
  let T : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) →
      ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) :=
    fun q => (q.1, (copyStat f N q.1 + q.2) / σ)
  let wt : ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) → ENNReal :=
    fun q => ENNReal.ofReal |σ| * w (q.1, σ * q.2 - copyStat f N q.1)
  let C : ℝ := σ * (β / 2) / Z ^ N
  let W : JointSpace N n → ℝ := fun p =>
    -potential V f β σ N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j)))
  have hZ : 0 < Z := integral_exp_pos hint
  have hσ : 0 < σ := by dsimp [σ, sigma]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hρ : Measurable ρ := hV.neg.exp.div_const Z
  have hH : Measurable H := by
    apply Finset.measurable_prod
    intro i _hi
    exact hρ.ennreal_ofReal.comp (measurable_pi_apply i)
  have hη : Measurable (fun s => ENNReal.ofReal (laplaceDensity β s)) := by
    unfold laplaceDensity
    fun_prop
  have hw : Measurable w := (hH.comp measurable_fst).mul (hη.comp measurable_snd)
  have hF : Measurable (copyStat f N) := by unfold copyStat; measurability
  have hT : Measurable T := measurable_fst.prodMk
    (((hF.comp measurable_fst).add measurable_snd).div_const σ)
  have hwt : Measurable wt := measurable_const.mul
    (hw.comp (measurable_fst.prodMk
      ((measurable_const.mul measurable_snd).sub (hF.comp measurable_fst))))
  have hpi : (Measure.pi fun _ : Fin N => μ) =
      (volume : Measure (Fin N → EuclideanSpace ℝ (Fin n))).withDensity H :=
    piWithDensityOfReal volume ρ hρ (fun _ => by dsimp [ρ]; positivity) N
  have hinput : (Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β) =
      (volume : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ)).withDensity w := by
    rw [hpi, laplaceMeasure, prod_withDensity hH hη, ← Measure.volume_eq_prod]
  have hmapT :
      ((volume : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ)).withDensity w).map T =
        (volume : Measure ((Fin N → EuclideanSpace ℝ (Fin n)) × ℝ)).withDensity wt := by
    simpa only [Measure.volume_eq_prod] using
      map_density_shift_scale (volume : Measure (Fin N → EuclideanSpace ℝ (Fin n)))
        (copyStat f N) hF σ hσ.ne' w hw
  obtain ⟨e, hef, hei, hevol⟩ := exists_raw_assembly_equiv N n
  have hembed : embed f σ N = e ∘ T := by
    funext q
    rw [Function.comp_apply, hef]
    rfl
  have hraw : Measurable (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      -potential V f β σ N (q.2, q.1)) := by
    unfold potential
    measurability
  have hWeq : W = (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
      -potential V f β σ N (q.2, q.1)) ∘ e.symm := by
    funext p
    rw [Function.comp_apply, hei]
  have hW : Measurable W := hWeq ▸ hraw.comp e.symm.measurable
  have hjoint : jointLaw μ f β σ N =
      (volume : Measure (JointSpace N n)).withDensity (fun p => wt (e.symm p)) := by
    rw [jointLaw, hembed, ← Measure.map_map e.measurable hT, hinput, hmapT,
      Probability.map_withDensity_measurableEquiv e volume wt hwt, hevol.map_eq]
  have hweight : ∀ p : JointSpace N n,
      wt (e.symm p) = ENNReal.ofReal (C * Real.exp (W p)) := by
    intro p
    rw [hei]
    exact joint_density_product V f hσ hZ (p none)
      (fun i => WithLp.toLp 2 fun j => p (some (i, j)))
  have hdensity : jointLaw μ f β σ N =
      (volume : Measure (JointSpace N n)).withDensity
        (fun p => ENNReal.ofReal (C * Real.exp (W p))) := by
    rw [hjoint]
    congr 1
    funext p
    exact hweight p
  let hpμ : IsProbabilityMeasure μ := isProbabilityMeasure_tilted hint
  have hpjoint : IsProbabilityMeasure (jointLaw μ f β σ N) :=
    isProbabilityMeasure_jointLaw_of_pos μ hf hβ σ N
  have hpweight : IsProbabilityMeasure ((volume : Measure (JointSpace N n)).withDensity
      (fun p => ENNReal.ofReal (C * Real.exp (W p)))) := hdensity ▸ hpjoint
  change jointLaw μ f β σ N = (volume : Measure (JointSpace N n)).tilted W
  exact hdensity.trans (normalized_of_probability_density volume W hW hC hpweight).2



open FunctionalInequalities.Analysis.BakryEmery in
/-- **The joint law is log-concave** under (110) (BKL p. 28, "Then `W_N` is convex"): (109) from
`jointLaw_eq_tilted` and convexity of `W_N` from `logConcave_jointLaw_of_eq_tilted`. -/
theorem logConcave_jointLaw {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ}
    (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x)))
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) :=
  logConcave_jointLaw_of_eq_tilted V f hβ hV hf hVa hfM hN
    (jointLaw_eq_tilted V f hβ hV.continuous.measurable hf.continuous.measurable hint) h

open scoped ContDiff in
/--
**Local exponential moments and smoothness of `Λ_ν` under (110)** (BKL p. 29, "the logarithmic
Laplace transform is finite and smooth in a neighborhood of the origin"): for `μ = e^{-V}dx/Z` with
`∇²V ≥ a`, `f ∈ C²` with `‖∇²f‖ ≤ M` and `β M/√N ≤ a`, the joint law has an exponential moment
`e^{r‖p‖}` for some `r > 0` and `Λ_ν` is `C^∞` on the ball of radius `r`. The density (109) is
proved, not assumed. -/
theorem exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw {n N : ℕ}
    (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V)
    (hf : ContDiff ℝ 2 f) (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (hint : Integrable (fun x => Real.exp (-V x))) :
    ∃ r : ℝ,
      0 < r ∧
        Integrable (fun p => Real.exp (r * ‖p‖))
            (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N) ∧
          ContDiffOn ℝ ∞
            (Analysis.BakryEmery.logLaplace
              (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N))
            (Metric.ball 0 r) := by
  have : IsProbabilityMeasure (volume.tilted fun x => -V x) := isProbabilityMeasure_tilted hint
  have hp :=
    isProbabilityMeasure_jointLaw_of_pos (volume.tilted fun x => -V x) hf.continuous.measurable
      hβ (sigma β) N
  exact
    (logConcave_jointLaw V f hβ hV hf hVa hfM hN hint
        hp).exists_integrable_exp_norm_contDiffOn_logLaplace

end FunctionalInequalities.KLS.LogConcave.Suspension
