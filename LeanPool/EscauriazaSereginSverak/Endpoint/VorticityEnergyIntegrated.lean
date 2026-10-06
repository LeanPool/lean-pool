/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityEnergySmooth
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityEnergyGronwall
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Time-integrated smooth vorticity energy

Compact spatial support lets the spatial differential estimate pass through
the time integral and the scalar Grönwall bound.
-/

public section


open MeasureTheory Set Filter
open scoped Topology
open scoped BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

private theorem vorticityEnergy_density_hasDerivAt
    {z : Vec3 × ℝ → Vec3}
    (hzcomp : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => z w i)) (t : ℝ) (x : Vec3) :
    HasDerivAt (fun s => ∑ i : Fin 3, (z (x, s) i) ^ 2)
      (2 * ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) t := by
  have htime (i : Fin 3) : HasDerivAt (fun s : ℝ => z (x, s) i)
      (CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t)) t := by
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => z (x, s) i) :=
      (hzcomp i).comp (contDiff_const.prodMk contDiff_id)
    have hd := (hslice.differentiable (by simp) t).hasDerivAt
    have hcoeff : deriv (fun s : ℝ => z (x, s) i) t =
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) := by
      unfold CKN.timePartial
      exact (fderiv_apply_one_eq_deriv).symm
    convert hd using 1
    exact hcoeff.symm
  have hpow (i : Fin 3) : HasDerivAt
      (fun s : ℝ => (z (x, s) i) ^ 2)
      (2 * CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) t := by
    convert (htime i).pow 2 using 1
    simp [mul_comm, mul_left_comm, mul_assoc]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i hi => hpow i)
  have hsumEq : (∑ i : Fin 3, 2 * CKN.timePartial
      (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) =
      2 * ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i := by
    calc
      _ = ∑ i : Fin 3, 2 *
          (CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  convert hsum using 1
  exact hsumEq.symm

private theorem vorticityEnergy_densityDerivative_continuous
    {z : Vec3 × ℝ → Vec3}
    (hzcomp : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => z w i)) :
    Continuous (Function.uncurry (fun (t : ℝ) (x : Vec3) =>
      2 * ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i)) := by
  have hswap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec3 => (p.2, p.1)) := contDiff_snd.prodMk contDiff_fst
  have h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun (t : ℝ) (x : Vec3) =>
      2 * ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i)) := by
    have htime (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun w : Vec3 × ℝ => CKN.timePartial (fun y : Vec3 × ℝ => z y i) w) :=
      CKN.contDiff_timePartial (hzcomp i)
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec3 =>
        ∑ i : Fin 3,
          CKN.timePartial (fun w : Vec3 × ℝ => z w i) (p.2, p.1) * z (p.2, p.1) i) := by
      apply ContDiff.sum (s := Finset.univ)
      intro i hi
      exact ((htime i).comp hswap).mul ((hzcomp i).comp hswap)
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec3 =>
      2 * ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (p.2, p.1) * z (p.2, p.1) i)
    exact contDiff_const.mul hsum
  exact h.continuous

private theorem vorticityEnergy_integrable_of_compact_space_support
    {K : Set Vec3} (hK : IsCompact K)
    {F : ℝ → Vec3 → ℝ} (hF : Continuous (Function.uncurry F))
    (hFzero : ∀ t x, x ∉ K → F t x = 0) (t : ℝ) :
    Integrable (F t) volume := by
  have hFc : HasCompactSupport (F t) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    change F t x ≠ 0 at hx
    by_contra hxK
    exact hx (hFzero t x hxK)
  have hFt : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  exact hFt.integrable_of_hasCompactSupport hFc

private theorem vorticityEnergy_continuous_integral_of_compact_space_support
    {K : Set Vec3} (hK : IsCompact K)
    {F : ℝ → Vec3 → ℝ} (hF : Continuous (Function.uncurry F))
    (hFzero : ∀ t x, x ∉ K → F t x = 0) :
    Continuous (fun t => ∫ x, F t x) := by
  have h := continuousOn_integral_of_compact_support (μ := volume) (s := univ)
    (k := K) hK hF.continuousOn (fun t x _ hx => hFzero t x hx)
  simpa using h

private theorem vorticityEnergy_hasDerivAt_integral_of_compact_space_support
    {K : Set Vec3} (hK : IsCompact K)
    {F F' : ℝ → Vec3 → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hFzero : ∀ t x, x ∉ K → F t x = 0)
    (hF'zero : ∀ t x, x ∉ K → F' t x = 0)
    (hderiv : ∀ t x, HasDerivAt (fun s => F s x) (F' t x) t) :
    ∀ t, HasDerivAt (fun t => ∫ x, F t x) (∫ x, F' t x) t := by
  intro t
  let Cball : Set ℝ := Metric.ball t 1
  let Kball : Set (ℝ × Vec3) := Metric.closedBall t 1 ×ˢ K
  have hKball : IsCompact Kball :=
    (isCompact_closedBall t 1).prod hK
  have hF'boundSet : BddAbove
      ((fun p : ℝ × Vec3 => ‖F' p.1 p.2‖) '' Kball) := by
    exact hKball.bddAbove_image (continuous_norm.comp_continuousOn hF'.continuousOn)
  obtain ⟨B, hB⟩ := hF'boundSet
  let A : ℝ := max B 0
  have hA : 0 ≤ A := le_max_right B 0
  have hAonKball : ∀ s x, (s, x) ∈ Kball → ‖F' s x‖ ≤ A := by
    intro s x hpair
    have himage : ‖F' s x‖ ∈
        (fun p : ℝ × Vec3 => ‖F' p.1 p.2‖) '' Kball :=
      ⟨(s, x), hpair, rfl⟩
    exact (hB himage).trans (le_max_left B 0)
  have hBound : ∀ᵐ x ∂volume, ∀ s ∈ Cball,
      ‖F' s x‖ ≤ K.indicator (fun _ : Vec3 => A) x := by
    filter_upwards [] with x
    intro s hs
    by_cases hx : x ∈ K
    · have hpair : (s, x) ∈ Kball := by
        exact ⟨Metric.mem_closedBall.mpr (le_of_lt hs), hx⟩
      simpa [Kball, A, Set.indicator_of_mem hx] using hAonKball s x hpair
    · rw [Set.indicator_of_notMem hx]
      have hzero := hF'zero s x hx
      simp [hzero]
  have hboundInt : Integrable (K.indicator (fun _ : Vec3 => A)) volume := by
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have hFslice (s : ℝ) : Continuous (F s) := by
    convert hF.comp (continuous_const.prodMk continuous_id) using 1
    · ext x
      rfl
  have hF'slice (s : ℝ) : Continuous (F' s) := by
    convert hF'.comp (continuous_const.prodMk continuous_id) using 1
    · ext x
      rfl
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun s => (hFslice s).aestronglyMeasurable)
    (vorticityEnergy_integrable_of_compact_space_support hK hF hFzero t)
    (hF'slice t).aestronglyMeasurable
    hBound hboundInt (Filter.Eventually.of_forall fun x s hs => by
      simpa [Function.comp_def, Function.uncurry] using hderiv s x)
  simpa [Function.comp_def, Function.uncurry] using hresult.2

private theorem vorticityEnergy_spatialPartial_zero_off_compact
    {K : Set Vec3} {z : Vec3 × ℝ → Vec3}
    (hK : IsCompact K) (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hzero : ∀ x, x ∉ K → ∀ t, z (x, t) = 0)
    {x : Vec3} (hx : x ∉ K) (t : ℝ) (i j : Fin 3) :
    CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t) = 0 := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => z (y, t) i) :=
    vorticityEnergy_slice_contDiff
      (vorticityEnergy_fieldComponent_contDiff hz i) t
  have hlocal : (fun y : Vec3 => z (y, t) i) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact congrFun (hzero y hy t) i
  have hfd : fderiv ℝ (fun y : Vec3 => z (y, t) i) x = 0 := by
    simpa using hlocal.fderiv_eq
  change (fderiv ℝ (fun y : Vec3 => z (y, t) i) x) (CKN.basisVec j) = 0
  rw [hfd]
  simp

private theorem vorticityEnergy_timePartial_zero_off_compact
    {K : Set Vec3} {z : Vec3 × ℝ → Vec3}
    (hzero : ∀ x, x ∉ K → ∀ t, z (x, t) = 0)
    {x : Vec3} (hx : x ∉ K) (t : ℝ) (i : Fin 3) :
    CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) = 0 := by
  have hslice : (fun s : ℝ => z (x, s) i) = fun _ => 0 := by
    funext s
    exact congrFun (hzero x hx s) i
  unfold CKN.timePartial
  rw [fderiv_apply_one_eq_deriv, hslice]
  simp

/-- A smooth, compactly supported solution of the linear vorticity equation
satisfies the time-integrated energy bound obtained from its spatial energy
inequality (manuscript `lem:localized-vorticity-energy`). -/
theorem smoothVorticityEnergyGronwall
    {a b M e₀ : ℝ}
    {v z : Vec3 × ℝ → Vec3} {F : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {g : Vec3 × ℝ → Vec3}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hz : ContDiff ℝ (⊤ : ℕ∞) z)
    (hF : ∀ j i, ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => F w j i))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcommon : ∃ K : Set Vec3, IsCompact K ∧
      ∀ x, x ∉ K → ∀ t,
        z (x, t) = 0 ∧ (∀ j i, F (x, t) j i = 0) ∧ g (x, t) = 0)
    (heq : ∀ (x : Vec3) (t : ℝ) (i : Fin 3),
      CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) -
        ∑ j : Fin 3, CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w => z w i) j j (x, t) =
      -(∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w =>
            v w j * z w i - z w j * v w i) j (x, t)) +
        ∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w => F w j i) j (x, t) +
        g (x, t) i)
    (hvbound : ∀ x t, vec3EuclideanNorm (v (x, t)) ≤ M)
    (hinit : (∫ x : Vec3, ∑ i : Fin 3, (z (x, a) i) ^ 2) ≤ e₀) :
    let e := fun t => ∫ x : Vec3, ∑ i : Fin 3, (z (x, t) i) ^ 2
    let d := fun t => ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
      (CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t)) ^ 2
    let f := fun t => 2 * (∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
      (F (x, t) j i) ^ 2) + (∫ x : Vec3, ∑ i : Fin 3, (g (x, t) i) ^ 2)
    (∀ t ∈ Icc a b,
      e t ≤ Real.exp ((72 * M ^ 2 + 1) * (b - a)) *
        (e₀ + (∫ s in a..b, f s))) ∧
    (∫ t in a..b, d t ≤ e₀ + (72 * M ^ 2 + 1) * (b - a) *
      (Real.exp ((72 * M ^ 2 + 1) * (b - a)) *
        (e₀ + (∫ s in a..b, f s))) + (∫ s in a..b, f s)) := by
  rcases hcommon with ⟨K, hK, hzero⟩
  let E : ℝ → Vec3 → ℝ := fun t x => ∑ i : Fin 3, (z (x, t) i) ^ 2
  let DE : ℝ → Vec3 → ℝ := fun t x =>
    2 * ∑ i : Fin 3,
      CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i
  let D : ℝ → Vec3 → ℝ := fun t x => ∑ j : Fin 3, ∑ i : Fin 3,
    (CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t)) ^ 2
  let P : ℝ → Vec3 → ℝ := fun t x => ∑ j : Fin 3, ∑ i : Fin 3,
    (F (x, t) j i) ^ 2
  let R : ℝ → Vec3 → ℝ := fun t x => ∑ i : Fin 3, (g (x, t) i) ^ 2
  have hzcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => z w i) :=
    vorticityEnergy_fieldComponent_contDiff hz i
  have hswap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec3 => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hEcont : Continuous (Function.uncurry E) := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry E) := by
      simp only [E]
      apply ContDiff.sum (s := Finset.univ)
      intro i hi
      exact ((hzcomp i).comp hswap).pow 2
    exact h.continuous
  have hDEcont : Continuous (Function.uncurry DE) := by
    simpa [DE] using vorticityEnergy_densityDerivative_continuous hzcomp
  have hDcont : Continuous (Function.uncurry D) := by
    have hgrad (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun w : Vec3 × ℝ =>
          CKN.spatialPartial (fun y : Vec3 × ℝ => z y i) j w) :=
      CKN.spatialPartial_contDiff (hzcomp i) j
    have h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry D) := by
      simp only [D]
      apply ContDiff.sum (s := Finset.univ)
      intro j hj
      apply ContDiff.sum (s := Finset.univ)
      intro i hi
      exact (((hgrad i j).comp hswap).pow 2)
    exact h.continuous
  have hPcont : Continuous (Function.uncurry P) := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry P) := by
      simp only [P]
      apply ContDiff.sum (s := Finset.univ)
      intro j hj
      apply ContDiff.sum (s := Finset.univ)
      intro i hi
      exact ((hF j i).comp (hswap)).pow 2
    exact h.continuous
  have hRcont : Continuous (Function.uncurry R) := by
    have hgcomp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun w : Vec3 × ℝ => g w i) :=
      (contDiff_apply ℝ ℝ i).comp hg
    have h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry R) := by
      simp only [R]
      apply ContDiff.sum (s := Finset.univ)
      intro i hi
      exact ((hgcomp i).comp hswap).pow 2
    exact h.continuous
  have hEzero : ∀ t x, x ∉ K → E t x = 0 := by
    intro t x hx
    simp only [E]
    apply Finset.sum_eq_zero
    intro i hi
    rw [congrFun (hzero x hx t).1 i]
    simp
  have hDEzero : ∀ t x, x ∉ K → DE t x = 0 := by
    intro t x hx
    simp only [DE]
    rw [show (∑ i : Fin 3,
      CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) = 0 by
        apply Finset.sum_eq_zero
        intro i hi
        rw [vorticityEnergy_timePartial_zero_off_compact (fun x hx t => (hzero x hx t).1)
          hx t i,
          congrFun (hzero x hx t).1 i]
        simp]
    ring
  have hDzero : ∀ t x, x ∉ K → D t x = 0 := by
    intro t x hx
    simp only [D]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro i hi
    rw [vorticityEnergy_spatialPartial_zero_off_compact hK hz
      (fun x hx t => (hzero x hx t).1) hx t i j]
    simp
  have hPzero : ∀ t x, x ∉ K → P t x = 0 := by
    intro t x hx
    simp only [P]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro i hi
    rw [(hzero x hx t).2.1 j i]
    simp
  have hRzero : ∀ t x, x ∉ K → R t x = 0 := by
    intro t x hx
    simp only [R]
    apply Finset.sum_eq_zero
    intro i hi
    rw [congrFun (hzero x hx t).2.2 i]
    simp
  have hEderiv : ∀ t x, HasDerivAt (fun s => E s x) (DE t x) t := by
    intro t x
    simpa [E, DE] using vorticityEnergy_density_hasDerivAt hzcomp t x
  have he : Continuous (fun t => ∫ x : Vec3, E t x) :=
    vorticityEnergy_continuous_integral_of_compact_space_support hK hEcont hEzero
  have hde : Continuous (fun t => ∫ x : Vec3, DE t x) :=
    vorticityEnergy_continuous_integral_of_compact_space_support hK hDEcont hDEzero
  have hd : Continuous (fun t => ∫ x : Vec3, D t x) :=
    vorticityEnergy_continuous_integral_of_compact_space_support hK hDcont hDzero
  have hp : Continuous (fun t => ∫ x : Vec3, P t x) :=
    vorticityEnergy_continuous_integral_of_compact_space_support hK hPcont hPzero
  have hr : Continuous (fun t => ∫ x : Vec3, R t x) :=
    vorticityEnergy_continuous_integral_of_compact_space_support hK hRcont hRzero
  let e : ℝ → ℝ := fun t => ∫ x : Vec3, E t x
  let de : ℝ → ℝ := fun t => ∫ x : Vec3, DE t x
  let d : ℝ → ℝ := fun t => ∫ x : Vec3, D t x
  let f : ℝ → ℝ := fun t => 2 * (∫ x : Vec3, P t x) + (∫ x : Vec3, R t x)
  have hde' : ∀ t, HasDerivAt e (de t) t := by
    intro t
    simpa [e, de] using
      vorticityEnergy_hasDerivAt_integral_of_compact_space_support
        hK hEcont hDEcont hEzero hDEzero hEderiv t
  have hf : Continuous f := by
    exact (continuous_const.mul hp).add hr
  have heIcc : ContinuousOn e (Icc a b) := he.continuousOn.congr fun t ht => by rfl
  have hepos : ∀ t ∈ Icc a b, 0 ≤ e t := by
    intro t ht
    apply integral_nonneg_of_ae
    filter_upwards [] with x
    exact Finset.sum_nonneg fun i hi => sq_nonneg (z (x, t) i)
  have hdpos : ∀ t ∈ Icc a b, 0 ≤ d t := by
    intro t ht
    apply integral_nonneg_of_ae
    filter_upwards [] with x
    exact Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun i hi =>
      sq_nonneg (CKN.spatialPartial (fun w : Vec3 × ℝ => z w i) j (x, t))
  have hfpos : ∀ t ∈ Icc a b, 0 ≤ f t := by
    intro t ht
    dsimp [f]
    have hpnonneg : 0 ≤ ∫ x : Vec3, P t x := by
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      exact Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun i hi =>
        sq_nonneg (F (x, t) j i)
    have hrnonneg : 0 ≤ ∫ x : Vec3, R t x := by
      apply integral_nonneg_of_ae
      filter_upwards [] with x
      exact Finset.sum_nonneg fun i hi => sq_nonneg (g (x, t) i)
    positivity
  have hderiv : ∀ t ∈ Ico a b, HasDerivAt e (de t) t := by
    intro t ht
    exact hde' t
  have hspatial := smoothVorticityEnergyDifferentialInequality_commonSupport
    hv hz hF hg ⟨K, hK, hzero⟩ heq M hM hvbound
  have hineq : ∀ t ∈ Icc a b,
      de t + d t ≤ (72 * M ^ 2 + 1) * e t + f t := by
    intro t ht
    change (∫ x : Vec3, DE t x) + (∫ x : Vec3, D t x) ≤
      (72 * M ^ 2 + 1) * (∫ x : Vec3, E t x) +
        (2 * (∫ x : Vec3, P t x) + (∫ x : Vec3, R t x))
    rw [show (∫ x : Vec3, DE t x) = 2 *
      (∫ x : Vec3, ∑ i : Fin 3,
        CKN.timePartial (fun w : Vec3 × ℝ => z w i) (x, t) * z (x, t) i) by
        simp [DE, integral_const_mul]]
    calc
      _ ≤ ((72 * M ^ 2 + 1) * (∫ x : Vec3, E t x) +
          2 * (∫ x : Vec3, P t x)) + (∫ x : Vec3, R t x) := by
        simpa [E, D, P, R] using hspatial t
      _ = (72 * M ^ 2 + 1) * (∫ x : Vec3, E t x) +
          (2 * (∫ x : Vec3, P t x) + (∫ x : Vec3, R t x)) := by ring
  have hederiv : ∀ t ∈ Ico a b, HasDerivAt e (de t) t := hderiv
  have hinit' : e a ≤ e₀ := by simpa [e, E] using hinit
  have hgronwall := vorticityEnergyGronwallDissipation hab
    (by positivity) heIcc hde hd hf hepos hdpos hfpos hederiv hineq hinit'
  simpa [e, d, f, E, D, P, R] using hgronwall

end

end ESS
