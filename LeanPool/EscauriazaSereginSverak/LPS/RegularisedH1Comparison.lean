/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Energy
public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsInJ
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDirectRoute
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# A common comparison interval for regularized H¹ energies

The scalar H¹ differential inequality gives the same lifespan for an entire
family of regularizations. The interval below has the fourth-power dependence
on the H¹ size used by `prop:lps-local-strong`.
-/

public section


open Set

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

namespace ESS.LPS

/-- A family satisfying one cubic H¹ differential inequality has a common
lifespan and a uniform energy plus dissipation bound. The interval depends
only on the common differential constant and the initial squared H¹ bound
(`prop:lps-local-strong`). -/
theorem lps_h1_family_common_lifespan_bound
    {ι : Type} {C E₀ : ℝ} (hC : 0 ≤ C) (hE₀ : 0 ≤ E₀)
    (y dy d : ι → ℝ → ℝ)
    (hy : ∀ k, Continuous (y k)) (hd : ∀ k, Continuous (d k))
    (henergy : ∀ k t, t ∈ Ioo 0
      (Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))) →
      HasDerivAt (y k) (dy k t) t)
    (hnonneg : ∀ k t, t ∈ Icc 0
      (Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))) →
      0 ≤ y k t ∧ 0 ≤ d k t)
    (hineq : ∀ k t, t ∈ Ioo 0
      (Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))) →
      dy k t + d k t ≤ C * (y k t) ^ 3)
    (hinit : ∀ k, y k 0 ≤ E₀) :
    0 < Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C)) ∧
      ∀ k t, t ∈ Icc 0
        (Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))) →
        y k t + ∫ s in 0..t, d k s ≤ 2 * (1 + E₀) := by
  let T : ℝ := Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))
  have hbase : 0 < 1 + Real.sqrt E₀ := by positivity
  have hT : 0 < T := by
    dsimp [T]
    exact div_pos (Real.rpow_pos_of_pos hbase _) (by positivity)
  have hroot : 0 ≤ Real.sqrt E₀ := Real.sqrt_nonneg E₀
  have hrootSq : (Real.sqrt E₀) ^ 2 = E₀ := Real.sq_sqrt hE₀
  have hpow : (1 + E₀) ^ 2 ≤ (1 + Real.sqrt E₀) ^ 4 := by
    have hsmall : 1 + (Real.sqrt E₀) ^ 2 ≤ (1 + Real.sqrt E₀) ^ 2 := by
      nlinarith only [sq_nonneg (Real.sqrt E₀), hroot]
    have hpow' := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (Real.sqrt E₀) ^ 2)
      hsmall (2 : ℕ)
    nlinarith only [hpow', hrootSq]
  have hTsmall : T - 0 ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2) := by
    have hden₁ : 0 < 8 * (1 + C) := by positivity
    have hden₂ : 0 < (1 + E₀) ^ 2 := by positivity
    have hquot :
        Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) =
          ((1 + Real.sqrt E₀) ^ 4)⁻¹ := by
      calc
        Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) =
            Real.rpow (1 + Real.sqrt E₀) (-(4 : ℝ)) := by norm_num
        _ = (Real.rpow (1 + Real.sqrt E₀) (4 : ℝ))⁻¹ :=
          Real.rpow_neg (le_of_lt hbase) (4 : ℝ)
        _ = ((1 + Real.sqrt E₀) ^ 4)⁻¹ := by
          congr 1
          exact Real.rpow_ofNat (1 + Real.sqrt E₀) 4
    have hInv' : 1 / ((1 + Real.sqrt E₀) ^ 4) ≤
        1 / ((1 + E₀) ^ 2) :=
      one_div_le_one_div_of_le hden₂ hpow
    have hInv : ((1 + Real.sqrt E₀) ^ 4)⁻¹ ≤ ((1 + E₀) ^ 2)⁻¹ := by
      simpa only [one_div] using hInv'
    change Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) /
      (8 * (1 + C)) - 0 ≤ 1 / (8 * (1 + C) * (1 + E₀) ^ 2)
    rw [sub_zero, hquot]
    calc
      ((1 + Real.sqrt E₀) ^ 4)⁻¹ / (8 * (1 + C)) ≤
          ((1 + E₀) ^ 2)⁻¹ / (8 * (1 + C)) :=
        div_le_div_of_nonneg_right hInv (by positivity)
      _ = 1 / (8 * (1 + C) * (1 + E₀) ^ 2) := by
        field_simp [ne_of_gt hden₁, ne_of_gt hden₂]
  refine ⟨hT, ?_⟩
  intro k t ht
  exact lps_h1_scalar_uniform_bound hC hE₀ (le_of_lt hT) hTsmall
    (hy k) (hd k) (henergy k) (hnonneg k) (hineq k) (hinit k) t ht

/-- The common scalar comparison controls both the spatial H¹ slices and
the integrated second-derivative dissipation once the kinetic energy is
bounded by the initial datum (`prop:lps-local-strong`). -/
theorem lps_h1_family_spatial_uniform_bound
    {ι : Type} {T E₀ : ℝ} (hT : 0 < T) (hE₀ : 0 ≤ E₀)
    (K G y d Q : ι → ℝ → ℝ)
    (hK : ∀ k t, t ∈ Icc 0 T → K k t ≤ E₀)
    (hG : ∀ k t, t ∈ Icc 0 T → G k t ≤ y k t)
    (hynonneg : ∀ k t, t ∈ Icc 0 T → 0 ≤ y k t)
    (hdnonneg : ∀ k t, t ∈ Icc 0 T → 0 ≤ d k t)
    (hcompare : ∀ k t, t ∈ Icc 0 T →
      y k t + ∫ s in 0..t, d k s ≤ 2 * (1 + E₀))
    (hQ : ∀ k, Q k T ≤ ∫ s in 0..T, d k s) :
    ∀ k, (∀ t, t ∈ Icc 0 T → K k t + G k t ≤ 3 * (1 + E₀)) ∧
      Q k T ≤ 3 * (1 + E₀) := by
  intro k
  have hSlice : ∀ t, t ∈ Icc 0 T → K k t + G k t ≤ 3 * (1 + E₀) := by
    intro t ht
    have hIntNonneg : 0 ≤ ∫ s in 0..t, d k s :=
      intervalIntegral.integral_nonneg ht.1 fun s hs =>
        hdnonneg k s ⟨hs.1, hs.2.trans ht.2⟩
    have hyBound : y k t ≤ 2 * (1 + E₀) := by
      have hc := hcompare k t ht
      linarith only [hc, hIntNonneg]
    have hKG := add_le_add (hK k t ht) (hG k t ht)
    nlinarith only [hKG, hyBound, hE₀]
  have hIntBound : ∫ s in 0..T, d k s ≤ 2 * (1 + E₀) := by
    have hIntNonneg : 0 ≤ ∫ s in 0..T, d k s :=
      intervalIntegral.integral_nonneg (le_of_lt hT) fun s hs =>
        hdnonneg k s ⟨hs.1, hs.2⟩
    have hc := hcompare k T ⟨le_of_lt hT, le_rfl⟩
    linarith only [hc, hynonneg k T ⟨le_of_lt hT, le_rfl⟩]
  constructor
  · exact hSlice
  · have hQbound := (hQ k).trans hIntBound
    nlinarith only [hQbound, hE₀]

/-- The scalar comparison interval determined by initial squared H¹ energy
and the cubic differential constant. -/
@[expose] def lpsH1ComparisonTime (E₀ C : ℝ) : ℝ :=
  Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))

/-- The componentwise squared H¹ energy of a good datum is integrable and
nonnegative (`prop:lps-local-strong`). -/
theorem lps_good_datum_h1_energy_integrable
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hGood : ESS.IsLpsGoodTime
      (fun z : ParabolicPoint => b z.1)
      (fun z i => Db z.1 i) 0) :
    Integrable (fun x : Vec3 =>
      (∑ i : Fin 3, (b x i) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2) volume ∧
      0 ≤ ∫ x : Vec3,
        (∑ i : Fin 3, (b x i) ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2 := by
  rcases hGood with ⟨hH1, hJ⟩
  have hb (i : Fin 3) : MemLp (fun x : Vec3 => b x i) 2 volume := by
    exact (memLp_pi_iff.mp hJ.1) i
  have hDb (i j : Fin 3) : MemLp (fun x : Vec3 => Db x i j) 2 volume := by
    obtain ⟨h, _hfun, hgrad⟩ := hH1 i
    have hmem : MemLp (fun x : Vec3 => h.grad x j) 2 volume := by
      simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
        CKN.volumeOn, Measure.restrict_univ] using h.gradMemL2 j
    simpa only [hgrad] using hmem
  have hbSq (i : Fin 3) : Integrable (fun x : Vec3 => (b x i) ^ 2) volume := by
    have h := (hb i).integrable_norm_pow (p := 2) (by norm_num)
    simpa [Real.norm_eq_abs] using h
  have hDbSq (i j : Fin 3) :
      Integrable (fun x : Vec3 => (Db x i j) ^ 2) volume := by
    have h := (hDb i j).integrable_norm_pow (p := 2) (by norm_num)
    simpa [Real.norm_eq_abs] using h
  have hVel : Integrable
      (fun x : Vec3 => ∑ i : Fin 3, (b x i) ^ 2) volume :=
    integrable_finsetSum _ fun i _ => hbSq i
  have hGrad : Integrable
      (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2) volume :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hDbSq i j
  refine ⟨hVel.add hGrad, ?_⟩
  exact integral_nonneg fun x => by positivity

/-- The scalar comparison and the regularized kinetic-energy estimate give
the exact ε-uniform slice-H¹ and space-time-H² bound used by the compactness
argument (`prop:lps-local-strong`). The assumptions are the PDE-derived
energy identities and physical norm identifications for this particular
regularized family. -/
theorem lps_regularised_uniform_h1_bounds_of_energy_estimates
    (ρ : CKN.Leray.RegMollifierProfile)
    (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hGood : ESS.IsLpsGoodTime
      (fun z : ParabolicPoint => b z.1)
      (fun z i => Db z.1 i) 0)
    (C : ℝ) (hC : 0 ≤ C)
    (y dy d : ℝ → ℝ → ℝ)
    (hy : ∀ ε, Continuous (y ε)) (hd : ∀ ε, Continuous (d ε))
    (henergy : ∀ ε (hε : 0 < ε) t,
      t ∈ Ioo 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      HasDerivAt (y ε) (dy ε t) t)
    (hnonneg : ∀ ε (hε : 0 < ε) t,
      t ∈ Icc 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      0 ≤ y ε t ∧ 0 ≤ d ε t)
    (hineq : ∀ ε (hε : 0 < ε) t,
      t ∈ Ioo 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      dy ε t + d ε t ≤ C * (y ε t) ^ 3)
    (hinit : ∀ ε (hε : 0 < ε),
      y ε 0 ≤ ∫ x : Vec3,
        (∑ i : Fin 3, (b x i) ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2)
    (hkinetic : ∀ ε (hε : 0 < ε) t,
      t ∈ Icc 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      ∫ x : Vec3,
        vec3EuclideanNorm
          (CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hGood.2)
            (x, t)) ^ (2 : ℕ) ≤
      ∫ x : Vec3,
        (∑ i : Fin 3, (b x i) ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2)
    (hgradient : ∀ ε (hε : 0 < ε) t,
      t ∈ Icc 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      ∫ x : Vec3,
        spatialGradientSq
          (CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hGood.2))
          (fun z i j => spatialPartial
            (fun w => CKN.Leray.regR12Velocity ρ ε hε b
              (by simpa using hGood.2) w i) j z) (x, t) ≤
        y ε t)
    (hkineticIntegrable : ∀ ε (hε : 0 < ε) t,
      t ∈ Icc 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      Integrable (fun x : Vec3 =>
        vec3EuclideanNorm
          (CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hGood.2)
            (x, t)) ^ (2 : ℕ)) volume)
    (hgradientIntegrable : ∀ ε (hε : 0 < ε) t,
      t ∈ Icc 0
        (Real.rpow
          (1 + Real.sqrt (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
          (-4 : ℝ) / (8 * (1 + C))) →
      Integrable (fun x : Vec3 =>
        spatialGradientSq
          (CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hGood.2))
          (fun z i j => spatialPartial
            (fun w => CKN.Leray.regR12Velocity ρ ε hε b
              (by simpa using hGood.2) w i) j z) (x, t)) volume)
    (hsecond : ∀ ε (hε : 0 < ε),
      ∫ z in spaceTimeSet (Set.univ : Set Vec3)
          (Ioo 0 (lpsH1ComparisonTime
            (∫ x : Vec3,
              (∑ i : Fin 3, (b x i) ^ 2) +
                ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2) C)),
        ∑ i : Fin 3, ∑ j : Fin 3,
          vec3EuclideanNorm
            (fun k => spatialPartial
              (fun w => spatialPartial
                (fun v => CKN.Leray.regR12Velocity ρ ε hε b
                  (by simpa using hGood.2) v i) j w) k z) ^ (2 : ℕ) ≤
      intervalIntegral (d ε) 0
        (lpsH1ComparisonTime
          (∫ x : Vec3,
            (∑ i : Fin 3, (b x i) ^ 2) +
              ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2) C) volume) :
    ∃ T M : ℝ, 0 < T ∧
      (1 / (8 * (1 + C))) * Real.rpow
        (1 + Real.sqrt (∫ x : Vec3,
          (∑ i : Fin 3, (b x i) ^ 2) +
            ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
        (-4 : ℝ) ≤ T ∧
      0 ≤ M ∧
      ∀ (ε : ℝ) (hε : 0 < ε),
        let Uε : ParabolicPoint → Vec3 :=
          CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hGood.2)
        let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
          spatialPartial (fun w => Uε w i) j z
        let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
          fun z i j k => spatialPartial
            (fun w => spatialPartial (fun v => Uε v i) j w) k z
        (∀ t : ℝ, t ∈ Icc 0 T →
          ∫ x : Vec3,
            vec3EuclideanNorm (Uε (x, t)) ^ (2 : ℕ) +
              spatialGradientSq Uε Dε (x, t) ≤ M) ∧
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ∑ i : Fin 3, ∑ j : Fin 3,
            vec3EuclideanNorm (D2ε z i j) ^ (2 : ℕ) ≤ M := by
  let E₀ : ℝ := ∫ x : Vec3,
    (∑ i : Fin 3, (b x i) ^ 2) +
      ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2
  let T₀ : ℝ := Real.rpow (1 + Real.sqrt E₀) (-4 : ℝ) / (8 * (1 + C))
  have hdata := lps_good_datum_h1_energy_integrable b Db hGood
  have hE₀ : 0 ≤ E₀ := by
    dsimp [E₀]
    exact hdata.2
  have hComparison := lps_h1_family_common_lifespan_bound
    (ι := {ε : ℝ // 0 < ε}) hC hE₀
    (fun ε t => y ε.1 t) (fun ε t => dy ε.1 t) (fun ε t => d ε.1 t)
    (fun ε => hy ε.1) (fun ε => hd ε.1)
    (by
      intro ε t ht
      simpa [T₀, E₀] using henergy ε.1 ε.2 t ht)
    (by
      intro ε t ht
      simpa [T₀, E₀] using hnonneg ε.1 ε.2 t ht)
    (by
      intro ε t ht
      simpa [T₀, E₀] using hineq ε.1 ε.2 t ht)
    (by
      intro ε
      simpa [E₀] using hinit ε.1 ε.2)
  obtain ⟨hT₀, hCompare⟩ := hComparison
  let K : {ε : ℝ // 0 < ε} → ℝ → ℝ := fun ε t =>
    ∫ x : Vec3, vec3EuclideanNorm
      (CKN.Leray.regR12Velocity ρ ε.1 ε.2 b (by simpa using hGood.2)
        (x, t)) ^ (2 : ℕ)
  let G : {ε : ℝ // 0 < ε} → ℝ → ℝ := fun ε t =>
    ∫ x : Vec3, spatialGradientSq
      (CKN.Leray.regR12Velocity ρ ε.1 ε.2 b (by simpa using hGood.2))
      (fun z i j => spatialPartial
        (fun w => CKN.Leray.regR12Velocity ρ ε.1 ε.2 b
          (by simpa using hGood.2) w i) j z) (x, t)
  let Q : {ε : ℝ // 0 < ε} → ℝ → ℝ := fun ε _ =>
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T₀),
      ∑ i : Fin 3, ∑ j : Fin 3,
        vec3EuclideanNorm
          (fun k => spatialPartial
            (fun w => spatialPartial
              (fun v => CKN.Leray.regR12Velocity ρ ε.1 ε.2 b
                (by simpa using hGood.2) v i) j w) k z) ^ (2 : ℕ)
  have hSpatial := lps_h1_family_spatial_uniform_bound
    hT₀ hE₀ K G (fun ε t => y ε.1 t) (fun ε t => d ε.1 t) Q
    (by
      intro ε t ht
      simpa [K, E₀] using hkinetic ε.1 ε.2 t (by simpa [T₀, E₀] using ht))
    (by
      intro ε t ht
      simpa [G] using hgradient ε.1 ε.2 t (by simpa [T₀, E₀] using ht))
    (by
      intro ε t ht
      exact (hnonneg ε.1 ε.2 t (by simpa [T₀, E₀] using ht)).1)
    (by
      intro ε t ht
      exact (hnonneg ε.1 ε.2 t (by simpa [T₀, E₀] using ht)).2)
    (by
      intro ε t ht
      simpa [T₀, E₀] using hCompare ε t (by simpa [T₀, E₀] using ht))
    (by
      intro ε
      exact hsecond ε.1 ε.2)
  refine ⟨T₀, 3 * (1 + E₀), hT₀, ?_, ?_, ?_⟩
  · dsimp [T₀, E₀]
    field_simp
    norm_num
  · positivity
  · intro ε hε
    let e : {ε : ℝ // 0 < ε} := ⟨ε, hε⟩
    let Uε : ParabolicPoint → Vec3 :=
      CKN.Leray.regR12Velocity ρ ε hε b (by simpa using hGood.2)
    let Dε : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun w => Uε w i) j z
    let D2ε : ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
      fun z i j k => spatialPartial
        (fun w => spatialPartial (fun v => Uε v i) j w) k z
    have hbnd := hSpatial e
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [integral_add
        (hkineticIntegrable ε hε t (by simpa [T₀, E₀] using ht))
        (hgradientIntegrable ε hε t (by simpa [T₀, E₀] using ht))]
      simpa [K, G, Uε, Dε, e, E₀] using
        hbnd.1 t (by simpa [T₀, E₀] using ht)
    · simpa [Q, D2ε, e, E₀, T₀] using hbnd.2

end ESS.LPS

end
