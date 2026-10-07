/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMollifierContraction
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegMollifierLemmaAssembly
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedEnergyAtTime
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedRHSL2
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedTimeChain
public import Mathlib.Analysis.MeanInequalities

/-!
# H¹ energy control for regularized solutions

The scalar comparison below is the lifespan step for the regularized H¹
energy identity. The PDE pairing supplies its cubic differential inequality.
-/

public section

open MeasureTheory Set
open scoped Interval


noncomputable section

namespace ESS.LPS

open CKN.Foundation.Parabolic
open CKN

private theorem lps_young_three_quarters
    {C E D : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : 0 ≤ D) :
    2 * C * Real.rpow E (3 / 4 : ℝ) * Real.rpow D (3 / 4 : ℝ) ≤
      4 * C ^ 4 * E ^ 3 + D := by
  let X : ℝ := 2 * C * Real.rpow E (3 / 4 : ℝ)
  let Y : ℝ := Real.rpow D (3 / 4 : ℝ)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hYpow : Real.rpow Y (4 / 3 : ℝ) = D := by
    dsimp [Y]
    convert Real.rpow_rpow_inv hD (by norm_num : (3 / 4 : ℝ) ≠ 0) using 1
    norm_num
  have hXpow : X ^ 4 = 16 * C ^ 4 * E ^ 3 := by
    dsimp [X]
    have hEpow : (Real.rpow E (3 / 4 : ℝ)) ^ 4 = E ^ 3 := by
      have hmul := Real.rpow_mul_natCast hE (3 / 4 : ℝ) 4
      norm_num [Real.rpow_natCast] at hmul
      simpa [Real.rpow_natCast] using hmul.symm
    calc
      (2 * C * Real.rpow E (3 / 4 : ℝ)) ^ 4 =
          16 * C ^ 4 * (Real.rpow E (3 / 4 : ℝ)) ^ 4 := by ring
      _ = 16 * C ^ 4 * E ^ 3 := congrArg (fun z : ℝ => 16 * C ^ 4 * z) hEpow
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hyoung : X * Y ≤
      (1 / 4 : ℝ) * X ^ 4 + (3 / 4 : ℝ) * Real.rpow Y (4 / 3 : ℝ) := by
    have h := Real.young_inequality_of_nonneg hX hY hpq
    norm_num [div_eq_mul_inv, Real.rpow_natCast] at h ⊢
    nlinarith only [h]
  have hscale :
      (1 / 4 : ℝ) * X ^ 4 + (3 / 4 : ℝ) * Real.rpow Y (4 / 3 : ℝ) ≤
        4 * C ^ 4 * E ^ 3 + D := by
    rw [hXpow, hYpow]
    nlinarith only [hD]
  calc
    2 * C * Real.rpow E (3 / 4 : ℝ) * Real.rpow D (3 / 4 : ℝ)
        = X * Y := by simp [X, Y]
    _ ≤ (1 / 4 : ℝ) * X ^ 4 + (3 / 4 : ℝ) * Real.rpow Y (4 / 3 : ℝ) := hyoung
    _ ≤ 4 * C ^ 4 * E ^ 3 + D := hscale

/-- The pressure-free regularized H¹ identity and its scale-independent
transport pairing estimate imply the cubic H¹ differential inequality. -/
theorem lps_h1_cubic_differential_inequality
    {C E D E' K : ℝ}
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hIdentity : E' + 2 * D = 2 * K)
    (hTransport : K ≤ C * Real.rpow E (3 / 4 : ℝ) *
      Real.rpow D (3 / 4 : ℝ)) :
    E' + D ≤ 4 * C ^ 4 * E ^ 3 := by
  have hYoung := lps_young_three_quarters hC hE hD
  have hK := mul_le_mul_of_nonneg_left hTransport (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [hIdentity, hK, hYoung]

/-- The initial regularization is an `L²` contraction on the spatial vector
field (`lem:reg-mollifier-bounds` of the CKN manuscript). -/
theorem lps_regularised_initial_velocity_l2_contraction
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (hb : MemLp b 2 volume) :
    eLpNorm (CKN.Leray.regUniformSpatialField
      (CKN.Leray.regUniformMollifiedInitial ρ ε hε b)) 2 volume ≤
      eLpNorm (CKN.Leray.regUniformSpatialField b) 2 volume := by
  have hcoord : MemLp (fun x : L2Vec3 => b (WithLp.ofLp x))
      2 volume :=
    hb.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  have hinput : MemLp (CKN.Leray.regUniformSpatialField b) 2 volume := by
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  change eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
      (CKN.Leray.regUniformSpatialField b)) 2 volume ≤
    eLpNorm (CKN.Leray.regUniformSpatialField b) 2 volume
  exact CKN.Leray.regMollifyVector_eLpNorm_two_le ρ ε hε hinput

/-- Each first-derivative row of the mollified initial state is an `L²`
contraction of the corresponding weak-gradient row
(`lem:reg-mollifier-bounds` of the CKN manuscript). -/
theorem lps_regularised_initial_gradient_row_l2_contraction
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : CKN.IsInJ b)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x => b x i) ∧ h.grad = (fun x j => Db x i j)) :
    ∀ i : Fin 3,
      eLpNorm (CKN.Leray.regUniformSpatialField
        (fun x j => spatialDeriv
          (fun y => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y i) j x))
          2 volume ≤
        eLpNorm (CKN.Leray.regUniformSpatialField (fun x => Db x i)) 2 volume := by
  have hDbLp (i j : Fin 3) : MemLp (fun x : Vec3 => Db x i j) 2 volume := by
    rcases hH1 i with ⟨h, _hfun, hgrad⟩
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ,
      hgrad] using h.gradMemL2 j
  have hDbLoc (i j : Fin 3) : LocallyIntegrable (fun x : Vec3 => Db x i j) volume :=
    (hDbLp i j).locallyIntegrable (by norm_num)
  have hweak (i j : Fin 3) :
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j
        (fun x : Vec3 => b x i) (fun x => Db x i j) := by
    rcases hH1 i with ⟨h, hfun, hgrad⟩
    have hh := h.hasWeakPartialDerivOn j
    rw [hfun, hgrad] at hh
    exact hh
  intro i
  let g : Vec3 → Vec3 := fun x j => Db x i j
  have hg : MemLp g 2 volume := (memLp_pi_iff).2 (fun j => hDbLp i j)
  have hrow :
      (fun x : Vec3 => fun j : Fin 3 => spatialDeriv
        (fun y => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y i) j x) =
      CKN.Leray.regUniformMollifiedInitial ρ ε hε g := by
    funext x
    funext j
    rw [CKN.Leray.regUniformMollifiedInitial_spatialDeriv_eq_weak
      ρ ε hε hb.1 (fun i j x => Db x i j) hDbLoc hweak x i j]
    rw [CKN.Leray.regUniformMollifiedInitial_component_convolution ρ ε hε hg x j]
    rfl
  have hcontract := lps_regularised_initial_velocity_l2_contraction ρ ε hε g hg
  rw [hrow]
  exact hcontract

/-- The total squared `H¹` energy of the mollified initial state is bounded
by the datum's squared `H¹` energy (`prop:lps-local-strong`). -/
theorem lps_regularised_initial_h1_energy_bound
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hb : CKN.IsInJ b)
    (hH1 : ∀ i : Fin 3, ∃ h : H1Function (Set.univ : Set Vec3),
      h.toFun = (fun x => b x i) ∧ h.grad = (fun x j => Db x i j)) :
    (eLpNorm (CKN.Leray.regUniformSpatialField
        (CKN.Leray.regUniformMollifiedInitial ρ ε hε b)) 2 volume) ^ (2 : ℕ) +
      ∑ i : Fin 3,
        (eLpNorm (CKN.Leray.regUniformSpatialField
          (fun x j => spatialDeriv
            (fun y => CKN.Leray.regUniformMollifiedInitial ρ ε hε b y i) j x))
            2 volume) ^ (2 : ℕ) ≤
      (eLpNorm (CKN.Leray.regUniformSpatialField b) 2 volume) ^ (2 : ℕ) +
      ∑ i : Fin 3,
        (eLpNorm (CKN.Leray.regUniformSpatialField (fun x => Db x i))
            2 volume) ^ (2 : ℕ) := by
  have hvel := lps_regularised_initial_velocity_l2_contraction ρ ε hε b hb.1
  have hvelSq := pow_le_pow_left₀ (by positivity) hvel (2 : ℕ)
  have hgrad i := lps_regularised_initial_gradient_row_l2_contraction
    ρ ε hε b Db hb hH1 i
  have hgradSq i := pow_le_pow_left₀ (by positivity) (hgrad i) (2 : ℕ)
  exact add_le_add hvelSq (Finset.sum_le_sum fun i _ => hgradSq i)

/-- A cubic H¹ energy inequality gives a uniform energy and dissipation bound
on a lifespan proportional to the inverse square of the initial energy
(`prop:lps-local-strong`). -/
theorem lps_h1_scalar_uniform_bound
    {a T C E₀ : ℝ} {y dy d : ℝ → ℝ}
    (hC : 0 ≤ C) (hE₀ : 0 ≤ E₀) (haT : a ≤ T)
    (hTsmall : T - a ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2))
    (hy : Continuous y) (hd : Continuous d)
    (henergy : ∀ t ∈ Ioo a T, HasDerivAt y (dy t) t)
    (hnonneg : ∀ t ∈ Icc a T, 0 ≤ y t ∧ 0 ≤ d t)
    (hineq : ∀ t ∈ Ioo a T, dy t + d t ≤ C * y t ^ 3)
    (hinit : y a ≤ E₀) :
    ∀ t ∈ Icc a T,
      y t + ∫ s in a..t, d s ≤ 2 * (1 + E₀) := by
  let F : ℝ → ℝ := fun t => ((1 + y t)⁻¹) ^ 2
  let G : ℝ → ℝ := fun t => -(F t + 2 * C * (t - a))
  have hden (t : ℝ) (ht : t ∈ Icc a T) : 0 < 1 + y t := by
    linarith only [(hnonneg t ht).1]
  have hFcont : ContinuousOn F (Icc a T) := by
    have hyI : ContinuousOn (fun t => 1 + y t) (Icc a T) :=
      continuousOn_const.add hy.continuousOn
    have hne : ∀ t ∈ Icc a T, 1 + y t ≠ 0 := fun t ht => (hden t ht).ne'
    change ContinuousOn (fun t => ((1 + y t)⁻¹) ^ 2) (Icc a T)
    exact (hyI.inv₀ hne).pow 2
  have hGcont : ContinuousOn G (Icc a T) := by
    have hlin : Continuous (fun t : ℝ => 2 * C * (t - a)) := by fun_prop
    exact (hFcont.add hlin.continuousOn).neg
  have hGderiv (t : ℝ) (ht : t ∈ Ioo a T) :
      HasDerivAt G (2 * dy t / (1 + y t) ^ 3 - 2 * C) t := by
    have htI : t ∈ Icc a T := ⟨ht.1.le, ht.2.le⟩
    have hden' : HasDerivAt (fun s : ℝ => 1 + y s) (dy t) t := by
      simpa using (henergy t ht).const_add (1 : ℝ)
    have hInv : HasDerivAt (fun s : ℝ => (1 + y s)⁻¹)
        (-dy t / (1 + y t) ^ 2) t := by
      exact hden'.inv (hden t htI).ne'
    have hFderiv : HasDerivAt F (-2 * dy t / (1 + y t) ^ 3) t := by
      have h := hInv.pow 2
      convert h using 1
      simp
      field_simp [ne_of_gt (hden t htI)]
    have hlinear : HasDerivAt (fun s : ℝ => 2 * C * (s - a)) (2 * C) t := by
      convert ((hasDerivAt_id t).const_mul (2 * C)).sub_const (2 * C * a) using 1
      · funext s
        simp
        ring
      · ring
    have hsum := hFderiv.add hlinear
    convert hsum.neg using 1
    ring
  have hGnonpos (t : ℝ) (ht : t ∈ Ioo a T) :
      2 * dy t / (1 + y t) ^ 3 - 2 * C ≤ 0 := by
    have htI : t ∈ Icc a T := ⟨ht.1.le, ht.2.le⟩
    have hdy : dy t ≤ C * y t ^ 3 := by
      have hd0 := (hnonneg t htI).2
      linarith only [hineq t ht, hd0]
    have hbase : y t ≤ 1 + y t := by linarith only [(hnonneg t htI).1]
    have hy0 := (hnonneg t htI).1
    have hpow : y t ^ 3 ≤ (1 + y t) ^ 3 := by gcongr
    have hnum : 2 * dy t ≤ 2 * C * (1 + y t) ^ 3 := by
      calc
        2 * dy t ≤ 2 * (C * y t ^ 3) := by nlinarith only [hdy]
        _ ≤ 2 * (C * (1 + y t) ^ 3) := by gcongr
        _ = 2 * C * (1 + y t) ^ 3 := by ring
    have hquot : 2 * dy t / (1 + y t) ^ 3 ≤ 2 * C :=
      (div_le_iff₀ (by positivity : 0 < (1 + y t) ^ 3)).2 hnum
    linarith only [hquot]
  have hGanti : AntitoneOn G (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a T) hGcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hGderiv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hGnonpos t ht
  have hFinit : 1 / (1 + E₀) ^ 2 ≤ F a := by
    have hya : 0 ≤ y a := (hnonneg a ⟨le_rfl, haT⟩).1
    have hdena : 0 < 1 + y a := hden a ⟨le_rfl, haT⟩
    have hdenE : 0 < 1 + E₀ := by linarith only [hE₀]
    have hdenle : 1 + y a ≤ 1 + E₀ := by linarith only [hinit]
    have hrecip : 1 / (1 + E₀) ≤ 1 / (1 + y a) :=
      one_div_le_one_div_of_le hdena hdenle
    have hsq : (1 / (1 + E₀)) ^ 2 ≤ (1 / (1 + y a)) ^ 2 := by gcongr
    simpa [F, one_div] using hsq
  have hloss (t : ℝ) (ht : t ∈ Icc a T) :
      2 * C * (t - a) ≤ 1 / (4 * (1 + E₀) ^ 2) := by
    have hdt : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hdtle : t - a ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2) := by
      calc
        t - a ≤ T - a := sub_le_sub_right ht.2 a
        _ ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2) := hTsmall
    have hratio : C / (1 + C) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : 0 < 1 + C)]
      linarith only [hC]
    calc
      2 * C * (t - a) ≤
          2 * C * (1 / (8 * (1 + C) * (1 + E₀) ^ 2)) :=
        mul_le_mul_of_nonneg_left hdtle (by positivity)
      _ = (C / (1 + C)) * (1 / (4 * (1 + E₀) ^ 2)) := by
        field_simp
        ring
      _ ≤ 1 / (4 * (1 + E₀) ^ 2) := by
        have hfactor : 0 ≤ 1 / (4 * (1 + E₀) ^ 2) := by positivity
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hfactor
  have hFbound (t : ℝ) (ht : t ∈ Icc a T) :
      1 / (4 * (1 + E₀) ^ 2) ≤ F t := by
    have hGle := hGanti ⟨le_rfl, haT⟩ ht ht.1
    change -(F t + 2 * C * (t - a)) ≤ -(F a + 2 * C * (a - a)) at hGle
    have hbase : 1 / (1 + E₀) ^ 2 =
        4 * (1 / (4 * (1 + E₀) ^ 2)) := by field_simp
    have htmp : 1 / (1 + E₀) ^ 2 ≤ F t + 2 * C * (t - a) := by
      linarith only [hGle, hFinit]
    rw [hbase] at htmp
    have hA : 0 ≤ 1 / (4 * (1 + E₀) ^ 2) := by positivity
    linarith only [htmp, hloss t ht, hA]
  have hybound (t : ℝ) (ht : t ∈ Icc a T) : y t ≤ 2 * (1 + E₀) := by
    have hdenpos := hden t ht
    have hEpos : 0 < 1 + E₀ := by linarith only [hE₀]
    have hFform : F t = 1 / (1 + y t) ^ 2 := by
      dsimp [F]
      field_simp [ne_of_gt hdenpos]
    have hsq : (1 + y t) ^ 2 ≤ 4 * (1 + E₀) ^ 2 := by
      have hf := hFbound t ht
      rw [hFform] at hf
      field_simp [ne_of_gt hdenpos, ne_of_gt hEpos] at hf
      nlinarith only [hf]
    have hqnonneg : 0 ≤ 1 + y t := by linarith only [hdenpos]
    have hEnonneg : 0 ≤ 2 * (1 + E₀) := by positivity
    have hroot : 1 + y t ≤ 2 * (1 + E₀) := by
      nlinarith only [hsq, hqnonneg, hEnonneg]
    linarith only [hroot]
  let Z : ℝ → ℝ := fun t => y t + (∫ s in a..t, d s) -
    C * (2 * (1 + E₀)) ^ 3 * (t - a)
  have hZcont : Continuous Z := by
    have hIcont : Continuous (fun t => ∫ s in a..t, d s) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      exact (hd.integral_hasStrictDerivAt a t).hasDerivAt.continuousAt
    have hlin : Continuous (fun t => C * (2 * (1 + E₀)) ^ 3 * (t - a)) := by
      fun_prop
    exact (hy.add hIcont).sub hlin
  have hZderiv (t : ℝ) (ht : t ∈ Ioo a T) :
      HasDerivAt Z (dy t + d t - C * (2 * (1 + E₀)) ^ 3) t := by
    have hIderiv : HasDerivAt (fun s => ∫ r in a..s, d r) (d t) t :=
      (hd.integral_hasStrictDerivAt a t).hasDerivAt
    have hlin : HasDerivAt (fun s => C * (2 * (1 + E₀)) ^ 3 * (s - a))
        (C * (2 * (1 + E₀)) ^ 3) t := by
      convert ((hasDerivAt_id t).const_mul (C * (2 * (1 + E₀)) ^ 3)).sub_const
        (C * (2 * (1 + E₀)) ^ 3 * a) using 1
      · funext s
        simp
        ring
      · ring
    have hsum := (henergy t ht).add hIderiv
    convert hsum.sub hlin using 1
  have hZnonpos (t : ℝ) (ht : t ∈ Ioo a T) :
      dy t + d t - C * (2 * (1 + E₀)) ^ 3 ≤ 0 := by
    have htI : t ∈ Icc a T := ⟨ht.1.le, ht.2.le⟩
    have henergy' := hineq t ht
    have hy3 : y t ^ 3 ≤ (2 * (1 + E₀)) ^ 3 := by
      have hnonnegY := (hnonneg t htI).1
      have hbound := hybound t htI
      gcongr
    have hmul := mul_le_mul_of_nonneg_left hy3 hC
    linarith only [henergy', hmul]
  have hZanti : AntitoneOn Z (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a T) hZcont.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hZderiv t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hZnonpos t ht
  intro t ht
  have hZle := hZanti ⟨le_rfl, haT⟩ ht ht.1
  have hZatA : Z a = y a := by simp [Z]
  have hZexpand : Z t = y t + (∫ s in a..t, d s) -
      C * (2 * (1 + E₀)) ^ 3 * (t - a) := by rfl
  have htime : t - a ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2) := by
    calc
      t - a ≤ T - a := sub_le_sub_right ht.2 a
      _ ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2) := hTsmall
  have hsource : C * (2 * (1 + E₀)) ^ 3 * (t - a) ≤ 1 + E₀ := by
    calc
      C * (2 * (1 + E₀)) ^ 3 * (t - a) ≤
          C * (2 * (1 + E₀)) ^ 3 *
            (1 / (8 * (1 + C) * (1 + E₀) ^ 2)) :=
        mul_le_mul_of_nonneg_left htime (by positivity)
      _ = (C / (1 + C)) * (1 + E₀) := by field_simp; ring
      _ ≤ 1 + E₀ := by
        have hratio : C / (1 + C) ≤ 1 := by
          rw [div_le_iff₀ (by positivity : 0 < 1 + C)]
          linarith only [hC]
        have hfactor : 0 ≤ 1 + E₀ := by linarith only [hE₀]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio hfactor
  rw [hZatA, hZexpand] at hZle
  have hbound := hybound t ht
  linarith only [hZle, hinit, hsource, hbound, hE₀]

end ESS.LPS

end
