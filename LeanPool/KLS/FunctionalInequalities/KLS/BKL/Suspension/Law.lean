/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Suspension.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.Line.Laplace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.KLS.FunctionalInequalities.KLS.Isotropic
public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.Tilted
public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Transport

/-!
# The joint law of the suspension (BKL Proposition 7.1)

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28. Let `X₁, …, X_N` be
independent with law `μ` on `ℝⁿ` and, independently, `η_β` Laplace with rate `β`. With
`F_N = N^{-1/2} Σ f(X_i)` and `σ_β² = 1 + 2/β²`, the vector `(S, X₁, …, X_N)`,
`S = (F_N + η_β)/σ_β`, lives in `ℝ^{Nn+1}`.

The joint space is modelled as `EuclideanSpace ℝ (Option (Fin N × Fin n))`: the coordinate `none`
is `S` and `some (i, j)` is the `j`-th coordinate of `X_i`, as in the source's indexing by `0` and
pairs `(i, j)`. `CumulantBound d b` names the hypothesis `R^ν_{d+1} ≤ b Id` of the proposition. This
module makes the definitions, proves that the joint law is a probability measure, and that it is
log-concave under (110) once it is identified with the tilted Lebesgue law of `W_N` (109).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open FunctionalInequalities.Probability.Line

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-- The joint space `ℝ^{Nn+1}`, indexed by `none` (the coordinate `S`) and pairs `(i, j)`. -/
abbrev JointSpace (N n : ℕ) : Type := EuclideanSpace ℝ (Option (Fin N × Fin n))

/-- The source's `σ_β = √(1 + 2/β²)`. -/
def sigma (β : ℝ) : ℝ := Real.sqrt (1 + 2 / β ^ 2)

/-- `σ_β² = 1 + 2/β²`. -/
theorem sigma_sq {β : ℝ} (hβ : 0 < β) :
    sigma β ^ 2 = 1 + 2 / β ^ 2 := by
  unfold sigma
  rw [Real.sq_sqrt]
  positivity

/-- **The limit `β → ∞`** (BKL p. 30): `X ≤ C σ_β²` for all `β > 0` forces `X ≤ C`. -/
theorem le_of_forall_le_mul_sigma_sq {X C : ℝ} (h : ∀ β : ℝ, 0 < β → X ≤ C * sigma β ^ 2) :
    X ≤ C := by
  by_contra hle
  have hCX : C < X := lt_of_not_ge hle
  by_cases hC : 0 ≤ C
  · let ε : ℝ := X - C
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * C / ε)
    have hnpos : 0 < n := by
      by_contra hn0
      have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst hnz
      have hnonneg : 0 ≤ 2 * C / ε := by
        positivity
      exact (not_lt_of_ge hnonneg) (by simpa using hn)
    have hnreal : 0 < (n : ℝ) := by
      exact_mod_cast hnpos
    have hnone : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnpos))
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith
    have hneps : 2 * C < ε * (n : ℝ) := by
      have h := (div_lt_iff₀ hε).mp hn
      nlinarith
    have hnepssq : 2 * C < ε * (n : ℝ) ^ 2 := by
      have hmul :
          ε * (n : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hnsq (le_of_lt hε)
      exact lt_of_lt_of_le hneps hmul
    have hfrac : 2 * C / (n : ℝ) ^ 2 < ε := by
      apply (div_lt_iff₀ (sq_pos_of_pos hnreal)).2
      exact hnepssq
    have hsmall : C * (1 + 2 / (n : ℝ) ^ 2) < X := by
      have heq :
          C * (1 + 2 / (n : ℝ) ^ 2) =
            C + 2 * C / (n : ℝ) ^ 2 := by
        ring
      rw [heq]
      dsimp [ε] at hfrac
      linarith
    have hlarge := h (n : ℝ) hnreal
    rw [sigma_sq hnreal] at hlarge
    exact (not_lt_of_ge hlarge) hsmall
  · have hCneg : C < 0 := lt_of_not_ge hC
    have hone := h 1 (by norm_num)
    rw [sigma_sq (by norm_num : (0 : ℝ) < 1)] at hone
    norm_num at hone
    nlinarith

/-- `F_N = N^{-1/2} Σ_i f(x_i)`. -/
def copyStat {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (N : ℕ)
    (x : Fin N → EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, f (x i)) / Real.sqrt N

/-- The map `(x₁, …, x_N, s) ↦ ((F_N(x) + s)/σ, x₁, …, x_N)` into the joint space. -/
def embed {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ) (N : ℕ)
    (q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) : JointSpace N n :=
  WithLp.toLp 2 fun o => Option.elim o ((copyStat f N q.1 + q.2) / σ) fun ij => q.1 ij.1 ij.2

/-- The joint law of `(S, X₁, …, X_N)`: the image of `μ^{⊗N} ⊗ η_β` under `embed`. -/
def jointLaw {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (β σ : ℝ) (N : ℕ) : Measure (JointSpace N n) :=
  ((Measure.pi fun _ : Fin N => μ).prod (laplaceMeasure β)).map (embed f σ N)

/-- `jointLaw μ f β σ N` is a probability measure when `μ` and `laplaceMeasure β` are and `f` is
measurable. -/
theorem isProbabilityMeasure_jointLaw {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    [IsProbabilityMeasure (laplaceMeasure β)] (σ : ℝ) (N : ℕ) :
    IsProbabilityMeasure (jointLaw μ f β σ N) := by
    have hg :
        Measurable
          (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
            fun o : Option (Fin N × Fin n) =>
              o.elim
                ((copyStat f N q.1 + q.2) / σ)
                (fun ij => (q.1 ij.1).ofLp ij.2)) := by
      rw [measurable_pi_iff]
      intro o
      cases o with
      | none =>
          unfold copyStat
          measurability
      | some ij =>
          measurability
    have h_embed : Measurable (embed f σ N) := by
      unfold embed
      exact (WithLp.measurable_toLp 2 _).comp hg
    refine ⟨?_⟩
    rw [jointLaw,
      Measure.map_apply_of_aemeasurable h_embed.aemeasurable MeasurableSet.univ]
    simp

/-- The joint law is a probability measure for every rate `β > 0` (the Laplace law's mass is
`isProbabilityMeasure_laplaceMeasure`). -/
theorem isProbabilityMeasure_jointLaw_of_pos {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    (hβ : 0 < β) (σ : ℝ) (N : ℕ) : IsProbabilityMeasure (jointLaw μ f β σ N) :=
  haveI := isProbabilityMeasure_laplaceMeasure hβ
  isProbabilityMeasure_jointLaw μ hf σ N

/-- **Log-concavity of the joint law under (110)**, given (109). -/
theorem logConcave_jointLaw_of_eq_tilted {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ)
    {a M β : ℝ} (hβ : 0 < β) (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hVa : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hN : β / Real.sqrt N * M ≤ a)
    (heq : jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
      (volume : Measure (JointSpace N n)).tilted fun p =>
        -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))))
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) := by
    let L : JointSpace N n →ₗ[ℝ] ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) :=
      { toFun := fun p =>
          (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))
        map_add' := by
          intro p q
          apply Prod.ext
          · simp
          · funext i
            ext j
            simp
        map_smul' := by
          intro c p
          apply Prod.ext
          · simp
          · funext i
            ext j
            simp }
    have hLcont :
        Continuous (fun p : JointSpace N n =>
          (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      fun_prop
    have hconv :
        ConvexOn ℝ Set.univ
          (fun p : JointSpace N n =>
            potential V f β (sigma β) N
              (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      simpa [L, Function.comp_def] using
        (convexOn_potential hV hf hβ.le hVa hfM N hN).comp_linearMap L
    have hpot :
        Continuous
          (fun q : ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) =>
            potential V f β (sigma β) N q) :=
      continuous_potential hV.continuous hf.continuous β (sigma β) N
    have hcont :
        Continuous
          (fun p : JointSpace N n =>
            potential V f β (sigma β) N
              (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      change Continuous
        ((fun q : ℝ × (Fin N → EuclideanSpace ℝ (Fin n)) =>
            potential V f β (sigma β) N q) ∘
          (fun p : JointSpace N n =>
            (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))))
      exact hpot.comp hLcont
    let ν : ProbabilityMeasure (JointSpace N n) :=
      ⟨jointLaw (volume.tilted fun x => -V x) f β (sigma β) N, h⟩
    have hν :
        (ν : Measure (JointSpace N n)) =
          (volume : Measure (JointSpace N n)).tilted
            (fun p =>
              -potential V f β (sigma β) N
                (p none, fun i => WithLp.toLp 2 (fun j => p (some (i, j))))) := by
      simpa [ν] using heq
    change KLS.LogConcave ν
    exact
      FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted
        hν hcont hconv

open scoped RealInnerProductSpace in
/-- The hypothesis of BKL Proposition 7.1: `R^ν_{d+1} ≤ b Id` for every isotropic log-concave
probability measure `ν` in every dimension, i.e. `Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²`
in the standard basis of `ℝ^m`. This names the hypothesis; it asserts nothing. -/
def CumulantBound (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν →
      _root_.FunctionalInequalities.KLS.LogConcave ν →
        ∀ u : EuclideanSpace ℝ (Fin m),
          ∑ J : Fin d → Fin m,
              Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                  (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^
                2 ≤
            b * ‖u‖ ^ 2

/-! ### The coordinate adapter `ℝ^{Option (Fin N × Fin n)} ≃ ℝ^{Nn+1}`

The hypothesis `CumulantBound` is stated for laws on `EuclideanSpace ℝ (Fin m)`; the joint law is
moved there by the linear isometry `coordinateEquiv`, which preserves isotropy
(`Isotropic.map_linearIsometryEquiv`), log-concavity and cumulants
(`cumulant_map_linearIsometryEquiv`). -/

/-- The index set of the joint space has `N n + 1` elements. -/
theorem card_option_prod (N n : ℕ) : Fintype.card (Option (Fin N × Fin n)) = N * n + 1 := by
  simp

/-- The coordinate reindexing of the joint space onto `ℝ^{Nn+1}`. -/
def coordinateEquiv (N n : ℕ) : JointSpace N n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (N * n + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFinOfCardEq (card_option_prod N n))

/-- `coordinateEquiv` sends standard basis vectors to standard basis vectors. -/
theorem coordinateEquiv_basisFun (N n : ℕ) (i : Option (Fin N × Fin n)) :
    coordinateEquiv N n (EuclideanSpace.basisFun _ ℝ i) =
      EuclideanSpace.basisFun (Fin (N * n + 1)) ℝ
        (Fintype.equivFinOfCardEq (card_option_prod N n) i) := by
  simp only [coordinateEquiv, EuclideanSpace.basisFun_apply, EuclideanSpace.piLpCongrLeft_single]

/-- Isotropy is preserved by the coordinate adapter. -/
theorem isotropic_map_coordinateEquiv {N n : ℕ} {ν : ProbabilityMeasure (JointSpace N n)}
    (hν : KLS.Isotropic ν) :
    KLS.Isotropic (ν.map (coordinateEquiv N n)) :=
  hν.map_linearIsometryEquiv (coordinateEquiv N n)

/-- Log-concavity is preserved by the coordinate adapter. -/
theorem logConcave_map_coordinateEquiv {N n : ℕ} {ν : ProbabilityMeasure (JointSpace N n)}
    (hν : KLS.LogConcave ν) :
    KLS.LogConcave (ν.map (coordinateEquiv N n)) := by
  let φ := coordinateEquiv N n
  apply KLS.LogConcave.of_affineIsometry_map hν
    (ν.map φ) φ.symm.toLinearIsometry.toAffineIsometry
  change Measure.map φ.symm (Measure.map φ (ν : Measure (JointSpace N n))) = _
  rw [Measure.map_map φ.symm.continuous.measurable φ.continuous.measurable]
  simp only [Function.comp_def, φ.symm_apply_apply, Measure.map_id']

open FunctionalInequalities.Analysis.BakryEmery in
/-- **`CumulantBound` on the joint space**, through the coordinate adapter: for an isotropic
log-concave `ν` on `JointSpace N n`, `Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²`, the sum
running over the joint index set (`cumulant_map_linearIsometryEquiv` pulls the cumulants back,
`Equiv.sum_comp` reindexes the sum). -/
theorem cumulantBound_jointSpace {N n d : ℕ} {b : ℝ} (hb : CumulantBound d b)
    {ν : ProbabilityMeasure (JointSpace N n)} (hiso : KLS.Isotropic ν) (hlc : KLS.LogConcave ν)
    (u : JointSpace N n) :
    ∑ J : Fin d → Option (Fin N × Fin n),
      cumulant (ν : Measure (JointSpace N n)) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2 := by
  classical
  let φ := coordinateEquiv N n
  let e := Fintype.equivFinOfCardEq (card_option_prod N n)
  have h := hb (N * n + 1) (ν.map φ)
    (isotropic_map_coordinateEquiv hiso) (logConcave_map_coordinateEquiv hlc) (φ u)
  rw [LinearIsometryEquiv.norm_map] at h
  refine le_trans (le_of_eq ?_) h
  rw [← (Equiv.piCongrRight fun _ : Fin d => e).sum_comp]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hmap : ((ν.map φ : ProbabilityMeasure _) :
      Measure (EuclideanSpace ℝ (Fin (N * n + 1)))) = (ν : Measure (JointSpace N n)).map φ := by
    simp [ProbabilityMeasure.toMeasure_map]
  rw [hmap]
  have hvec : (Fin.cons (φ u) fun k => EuclideanSpace.basisFun (Fin (N * n + 1)) ℝ
      ((Equiv.piCongrRight fun _ : Fin d => e) J k)) =
      fun i => φ ((Fin.cons u fun k => EuclideanSpace.basisFun _ ℝ (J k) : Fin (d + 1) → _) i) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp
    · simp only [Fin.cons_succ, Equiv.piCongrRight_apply]
      exact (coordinateEquiv_basisFun N n (J k)).symm
  rw [hvec, cumulant_map_linearIsometryEquiv]

end FunctionalInequalities.KLS.LogConcave.Suspension
