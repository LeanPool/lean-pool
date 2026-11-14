/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffPotentialLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedIdentities

/-!
# PenalizedResolventIdentity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Resolvent identity for the penalized cubic supremum

For a fixed exterior penalty, the bounded-domain resolvent identity passes
through both cubic exhaustions.  The required pointwise passage for the inner
datum uses local freezing, so the continuous skew part may have arbitrary
size.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- Applying a fixed outer penalized cube resolvent commutes with the
increasing exhaustion limit of the inner penalized resolvents. -/
theorem tendsto_analyticPenalizedCubeResolvent_comp {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu nu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (outer : ℕ) (x : Vec d) :
    let g : Vec d → ℝ := fun y ↦
      (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal
    Tendsto (fun k ↦ A.analyticPenalizedCubeResolvent hV n nu
        (A.analyticPenalizedCubeResolvent hV n mu f hf hfD k)
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
        (D := D / (mu : ℝ))
        (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD k)
        outer x) atTop
      (nhds (A.analyticPenalizedCubeResolvent hV n nu g
        (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
        (D := D / (mu : ℝ)) (fun y ↦ by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal
            (div_nonneg hD mu.property.le)
            (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD y))
        outer x)) := by
  dsimp only
  by_cases hx : x ∈ wholeSpaceCube d outer
  · let hU := isOpenBoundedConvexDomain_wholeSpaceCube d outer
    let q : Vec d → ℝ := wholeSpacePenalizationPotential V n
    let hq := wholeSpacePenalizationPotential_isBounded hV n outer
    let gk : ℕ → Vec d → ℝ := fun k ↦
      A.analyticPenalizedCubeResolvent hV n mu f hf hfD k
    let g : Vec d → ℝ := fun y ↦
      (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal
    let hg : Measurable g :=
      (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
    let C : ℝ := D / (mu : ℝ)
    let B : ℝ := C / (nu : ℝ)
    have hC : 0 ≤ C := div_nonneg hD mu.property.le
    have hB : 0 ≤ B := div_nonneg hC nu.property.le
    have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y ↦
      A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD k y
    have hg0 : ∀ y, 0 ≤ g y := fun _ ↦ ENNReal.toReal_nonneg
    have hgBound : ∀ y, |g y| ≤ C := by
      intro y
      rw [abs_of_nonneg (hg0 y)]
      exact ENNReal.toReal_le_of_le_ofReal hC
        (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD y)
    let Fk : ℕ → ScalarL2 (wholeSpaceCube d outer) := fun k ↦
      boundedMeasurableToScalarL2 hU
        ((A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k).comp
          measurable_subtype_coe) (fun y ↦ hgkBound k y)
    let Fl : ScalarL2 (wholeSpaceCube d outer) :=
      boundedMeasurableToScalarL2 hU (hg.comp measurable_subtype_coe)
        (fun y ↦ hgBound y)
    have hFk : ∀ k, Fk k =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
        domainExtension (gk k ∘ Subtype.val) := fun k ↦
      boundedMeasurableToScalarL2_coeFn hU
        ((A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k).comp
          measurable_subtype_coe) (fun y ↦ hgkBound k y)
    have hFl : Fl =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
        domainExtension (g ∘ Subtype.val) :=
      boundedMeasurableToScalarL2_coeFn hU
        (hg.comp measurable_subtype_coe) (fun y ↦ hgBound y)
    have hpt : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        Tendsto (fun k ↦ Fk k y) atTop (nhds (Fl y)) := by
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      rw [hyl, domainExtension_of_mem hyU]
      have ht := A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0
        hD hfD y
      apply ht.congr'
      filter_upwards with k
      rw [hyk k, domainExtension_of_mem hyU]
      rfl
    have hdiff : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        ∀ k, |Fk k y - Fl y| ≤ 2 * C := by
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      intro k
      rw [hyk k, hyl, domainExtension_of_mem hyU,
        domainExtension_of_mem hyU]
      calc
        |gk k y - g y| ≤ |gk k y| + |g y| := abs_sub _ _
        _ ≤ C + C := add_le_add (hgkBound k y) (hgBound y)
        _ = 2 * C := by ring
    have hnorm : Tendsto (fun k ↦ ‖Fk k - Fl‖) atTop (nhds 0) :=
      tendsto_norm_scalarL2_sub_of_bounded_ae_tendsto hU hdiff hpt
    let wk : ℕ → Vec d → ℝ := fun k ↦
      A.analyticPenalizedCubeResolvent hV n nu (gk k)
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
        (hgkBound k) outer
    let w : Vec d → ℝ :=
      A.analyticPenalizedCubeResolvent hV n nu g hg hgBound outer
    have hwkBound : ∀ k y, |wk k y| ≤ B := fun k y ↦
      A.abs_analyticPenalizedCubeResolvent_le hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
        hC (hgkBound k) outer y
    have hwBound : ∀ y, |w y| ≤ B := fun y ↦
      A.abs_analyticPenalizedCubeResolvent_le hV n nu hg hC hgBound outer y
    have hwkae : ∀ k, wk k =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
        potentialResolvent A.a nu.property A.hnu (A.cubeEllipticity outer)
          q hq (Fk k) := by
      intro k
      simpa only [wk, q, hq, Fk, gk] using
        A.analyticPenalizedCubeResolvent_ae hV n nu
          (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
          (hgkBound k) outer
    have hwae : w =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
        potentialResolvent A.a nu.property A.hnu (A.cubeEllipticity outer)
          q hq Fl := by
      simpa only [w, q, hq, Fl, g, hg] using
        A.analyticPenalizedCubeResolvent_ae hV n nu hg hgBound outer
    let P : ScalarL2 (wholeSpaceCube d outer) →L[ℝ]
        ScalarL2 (wholeSpaceCube d outer) :=
      potentialResolvent A.a nu.property A.hnu (A.cubeEllipticity outer) q hq
    let Q : ScalarL2 (wholeSpaceCube d outer) →L[ℝ]
        ScalarL2 (wholeSpaceCube d outer) := potentialMul q hq
    have hEff : ∀ k, ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        |(Fk k - Q (P (Fk k))) y - (Fl - Q (P Fl)) y| ≤
          2 * C + (n : ℝ) * (2 * B) := by
      intro k
      filter_upwards [hdiff.mono fun _ hy ↦ hy k, hwkae k, hwae,
        potentialMul_coeFn q hq (P (Fk k)), potentialMul_coeFn q hq (P Fl),
        Lp.coeFn_sub (Fk k) (Q (P (Fk k))),
        Lp.coeFn_sub Fl (Q (P Fl))] with y hraw hwkRep hwRep hmulK hmulL
          hsubK hsubL
      rw [hsubK, hsubL]
      simp only [Pi.sub_apply]
      rw [hmulK, hmulL]
      have hq0 : 0 ≤ q y := wholeSpacePenalizationPotential_nonneg V n y
      have hqN : q y ≤ n := wholeSpacePenalizationPotential_le V n y
      have hwdiff : |P (Fk k) y - P Fl y| ≤ 2 * B := by
        rw [← hwkRep, ← hwRep]
        exact (abs_sub _ _).trans (by
          simpa only [two_mul] using add_le_add (hwkBound k y) (hwBound y))
      calc
        |(Fk k y - q y * P (Fk k) y) - (Fl y - q y * P Fl y)| =
            |(Fk k y - Fl y) - q y * (P (Fk k) y - P Fl y)| := by
          congr 1
          ring
        _ ≤ |Fk k y - Fl y| + |q y * (P (Fk k) y - P Fl y)| :=
          abs_sub _ _
        _ = |Fk k y - Fl y| + q y * |P (Fk k) y - P Fl y| := by
          rw [abs_mul, abs_of_nonneg hq0]
        _ ≤ 2 * C + (n : ℝ) * (2 * B) :=
          add_le_add hraw
            (mul_le_mul hqN hwdiff (abs_nonneg _) (Nat.cast_nonneg n))
    exact tendsto_potentialRepresentative_of_tendsto_norm_continuousCoeff
      A.a hU nu.property A.hnu (A.cubeEllipticity outer) A.hsymm
      (A.skewContinuousOnCube outer) A.hd q hq
      (M := 2 * C + (n : ℝ) * (2 * B))
      (add_nonneg (mul_nonneg (by norm_num) hC)
        (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (by norm_num) hB)))
      hEff hnorm
      (fun k ↦ A.continuousOn_analyticPenalizedCubeResolvent hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
        (hgkBound k) outer)
      hwkae
      (A.continuousOn_analyticPenalizedCubeResolvent hV n nu hg hgBound outer)
      hwae hx
  · simp only [analyticPenalizedCubeResolvent, dite_eq_right hx]
    exact tendsto_const_nhds

/-- The diagonal of the two cubic exhaustions computes the composition of
two minimal resolvents with the same exterior penalty. -/
theorem analyticPenalizedResolvent_comp_eq_iSup {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (nu mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    let g : Vec d → ℝ := fun y ↦
      (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal
    (A.analyticPenalizedResolvent hV n nu g
        (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
        (D := D / (mu : ℝ)) (fun y ↦ by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal
            (div_nonneg hD mu.property.le)
            (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD y)) x).toReal =
      ⨆ m, A.analyticPenalizedCubeResolvent hV n nu
        (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m)
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
        (D := D / (mu : ℝ))
        (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m) m x := by
  dsimp only
  let gk : ℕ → Vec d → ℝ := fun k ↦
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD k
  let g : Vec d → ℝ := fun y ↦
    (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal
  let C : ℝ := D / (mu : ℝ)
  have hC : 0 ≤ C := div_nonneg hD mu.property.le
  have hgk0 : ∀ k y, 0 ≤ gk k y := fun k y ↦
    A.analyticPenalizedCubeResolvent_nonneg hV n mu hf hf0 hfD k y
  have hg0 : ∀ y, 0 ≤ g y := fun _ ↦ ENNReal.toReal_nonneg
  have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y ↦
    A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD k y
  have hgBound : ∀ y, |g y| ≤ C := by
    intro y
    rw [abs_of_nonneg (hg0 y)]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD y)
  let a : ℕ → ℕ → ℝ := fun outer k ↦
    A.analyticPenalizedCubeResolvent hV n nu (gk k)
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
      (hgkBound k) outer x
  have haMonoLeft : ∀ k, Monotone fun outer ↦ a outer k := by
    intro k
    exact A.monotone_analyticPenalizedCubeResolvent hV n nu
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
      (hgk0 k) (hgkBound k) x
  have hgkMono : Monotone gk := by
    intro i j hij y
    exact A.monotone_analyticPenalizedCubeResolvent hV n mu hf hf0 hfD y hij
  have haMonoRight : ∀ outer, Monotone (a outer) := by
    intro outer i j hij
    exact A.analyticPenalizedCubeResolvent_mono hV n nu
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD i)
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD j)
      (hgkBound i) (hgkBound j) (hgkMono hij) outer x
  have haBdd : ∀ outer, BddAbove (Set.range (a outer)) := by
    intro outer
    refine ⟨C / (nu : ℝ), ?_⟩
    rintro y ⟨k, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticPenalizedCubeResolvent_le hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
        hC (hgkBound k) outer x)
  have hrow : ∀ outer,
      A.analyticPenalizedCubeResolvent hV n nu g
          (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
          hgBound outer x = ⨆ k, a outer k := by
    intro outer
    exact tendsto_nhds_unique
      (A.tendsto_analyticPenalizedCubeResolvent_comp hV n mu nu hf hf0 hD
        hfD outer x)
      (tendsto_atTop_ciSup (haMonoRight outer) (haBdd outer))
  have hleft := A.tendsto_analyticPenalizedCubeResolvent hV n nu
    (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
    hg0 hC hgBound x
  have hleftSup :
      (A.analyticPenalizedResolvent hV n nu g
        (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
        hgBound x).toReal = ⨆ outer,
          A.analyticPenalizedCubeResolvent hV n nu g
            (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
            hgBound outer x := by
    apply tendsto_nhds_unique hleft
    exact tendsto_atTop_ciSup
      (A.monotone_analyticPenalizedCubeResolvent hV n nu
        (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
        hg0 hgBound x)
      (by
        refine ⟨C / (nu : ℝ), ?_⟩
        rintro y ⟨outer, rfl⟩
        exact (le_abs_self _).trans
          (A.abs_analyticPenalizedCubeResolvent_le hV n nu
            (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
            hC hgBound outer x))
  rw [hleftSup]
  simp_rw [hrow]
  change (⨆ outer, ⨆ k, a outer k) = ⨆ m, a m m
  have hdiagBdd : BddAbove (Set.range fun m ↦ a m m) := by
    refine ⟨C / (nu : ℝ), ?_⟩
    rintro y ⟨m, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticPenalizedCubeResolvent_le hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
        hC (hgkBound m) m x)
  have hrowsBdd : BddAbove (Set.range fun outer ↦ ⨆ k, a outer k) := by
    refine ⟨C / (nu : ℝ), ?_⟩
    rintro y ⟨outer, rfl⟩
    exact ciSup_le fun k ↦ (le_abs_self _).trans
      (A.abs_analyticPenalizedCubeResolvent_le hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD k)
        hC (hgkBound k) outer x)
  apply le_antisymm
  · refine ciSup_le fun outer ↦ ciSup_le fun k ↦ ?_
    exact le_ciSup_of_le hdiagBdd (max outer k)
      ((haMonoLeft k (le_max_left outer k)).trans
        (haMonoRight (max outer k) (le_max_right outer k)))
  · refine ciSup_le fun m ↦ ?_
    exact le_ciSup_of_le hrowsBdd m (le_ciSup (haBdd m) m)

/-- The real minimal resolvents with a fixed exterior penalty satisfy the
resolvent identity on nonnegative bounded measurable data. -/
theorem analyticPenalizedResolvent_toReal_resolventIdentity
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ)
    (mu nu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal =
      (A.analyticPenalizedResolvent hV n nu f hf hfD x).toReal +
        ((nu : ℝ) - (mu : ℝ)) *
          (A.analyticPenalizedResolvent hV n nu
            (fun y ↦ (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal)
            (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
            (D := D / (mu : ℝ)) (fun y ↦ by
              rw [abs_of_nonneg ENNReal.toReal_nonneg]
              exact ENNReal.toReal_le_of_le_ofReal
                (div_nonneg hD mu.property.le)
                (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD y))
            x).toReal := by
  let gk : ℕ → Vec d → ℝ := fun m ↦
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m
  let C : ℝ := D / (mu : ℝ)
  have hC : 0 ≤ C := div_nonneg hD mu.property.le
  have hgk0 : ∀ m y, 0 ≤ gk m y := fun m y ↦
    A.analyticPenalizedCubeResolvent_nonneg hV n mu hf hf0 hfD m y
  have hgkBound : ∀ m y, |gk m y| ≤ C := fun m y ↦
    A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m y
  let c : ℕ → ℝ := fun m ↦
    A.analyticPenalizedCubeResolvent hV n nu (gk m)
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
      (hgkBound m) m x
  have hgkMono : Monotone gk := by
    intro i j hij y
    exact A.monotone_analyticPenalizedCubeResolvent hV n mu hf hf0 hfD y hij
  have hcMono : Monotone c := by
    refine monotone_nat_of_le_succ fun m ↦ ?_
    exact (A.monotone_analyticPenalizedCubeResolvent hV n nu
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
      (hgk0 m) (hgkBound m) x (Nat.le_succ m)).trans
      (A.analyticPenalizedCubeResolvent_mono hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD (m + 1))
        (hgkBound m) (hgkBound (m + 1))
        (hgkMono (Nat.le_succ m)) (m + 1) x)
  have hcBdd : BddAbove (Set.range c) := by
    refine ⟨C / (nu : ℝ), ?_⟩
    rintro y ⟨m, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticPenalizedCubeResolvent_le hV n nu
        (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
        hC (hgkBound m) m x)
  have hcTendsto : Tendsto c atTop (nhds
      (A.analyticPenalizedResolvent hV n nu
        (fun y ↦ (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal)
        (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal
        (D := C) (fun y ↦ by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal hC
            (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD y))
        x).toReal) := by
    rw [A.analyticPenalizedResolvent_comp_eq_iSup hV n nu mu hf hf0 hD hfD x]
    exact tendsto_atTop_ciSup hcMono hcBdd
  have hconst : Tendsto (fun _ : ℕ ↦ (nu : ℝ) - (mu : ℝ)) atTop
      (nhds ((nu : ℝ) - (mu : ℝ))) := tendsto_const_nhds
  have hright :=
    (A.tendsto_analyticPenalizedCubeResolvent hV n nu hf hf0 hD hfD x).add
      (hconst.mul hcTendsto)
  apply tendsto_nhds_unique
    (A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0 hD hfD x)
  apply hright.congr'
  filter_upwards with m
  exact A.analyticPenalizedCubeResolvent_resolventIdentity hV n mu nu hf hD
    hfD m x |>.symm

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
