/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import LeanPool.EllipticPDE.Analysis.LpTranslation


/-!
# Fréchet-Kolmogorov precompactness criterion in `L²(ℝⁿ)`

A family of `L²` functions that is uniformly bounded, supported in a fixed ball, and
uniformly Lipschitz under translation is totally bounded in `L²(ℝⁿ)`. This is the
Fréchet-Kolmogorov (Riesz-Kolmogorov) criterion, the precompactness engine behind the
Rellich-Kondrachov compact embedding.

The proof approximates each member of the family by its average over a fixed grid of
axis-aligned cubes of side `η`. The averaging operator lands in the finite-dimensional
span of the cube indicators, so its image is totally bounded; the approximation error is
controlled by the translation modulus through a cube-averaging estimate that reuses the
squared-Tonelli pattern of `MeasureTheory.integral_sq_sub_translation_le`. A finite net of
the averaged family, widened by the uniform approximation error, is a finite net of the
original family.

## Main results

* `MeasureTheory.sq_setIntegral_le`: the finite-measure Cauchy-Schwarz bound
  `(∫_s f)² ≤ μ.real s * ∫_s f²`.
* `MeasureTheory.totallyBounded_of_lipschitz_translation`: the Fréchet-Kolmogorov criterion.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- **Approximation by totally bounded sets.** If every member of `S` is approximable to arbitrary
precision by a totally bounded set, then `S` is totally bounded. -/
theorem totallyBounded_of_approx {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (h : ∀ ε > 0, ∃ T : Set X, TotallyBounded T ∧ ∀ s ∈ S, ∃ t ∈ T, dist s t < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨T, hT, hST⟩ := h (ε / 2) (by linarith)
  rw [Metric.totallyBounded_iff] at hT
  obtain ⟨F, hFfin, hTF⟩ := hT (ε / 2) (by linarith)
  refine ⟨F, hFfin, fun s hs => ?_⟩
  obtain ⟨t, htT, hst⟩ := hST s hs
  obtain ⟨f, hfF, htf⟩ := mem_iUnion₂.mp (hTF htT)
  rw [Metric.mem_ball] at htf
  refine mem_iUnion₂.mpr ⟨f, hfF, ?_⟩
  rw [Metric.mem_ball]
  calc dist s f ≤ dist s t + dist t f := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Total boundedness inside a finite-dimensional subspace.** A bounded subset of a
finite-dimensional subspace of a real normed space is totally bounded in the ambient space. -/
theorem totallyBounded_of_finiteDimensional_bounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (V : Submodule ℝ E) [FiniteDimensional ℝ V] {T : Set E}
    (hTV : T ⊆ (V : Set E)) (hT : Bornology.IsBounded T) : TotallyBounded T := by
  have hrange : T ⊆ Set.range V.subtypeₗᵢ := fun t ht => ⟨⟨t, hTV ht⟩, rfl⟩
  have hpre : Bornology.IsBounded (V.subtypeₗᵢ ⁻¹' T) :=
    V.subtypeₗᵢ.isometry.antilipschitzWith.isBounded_preimage hT
  have htb : TotallyBounded (V.subtypeₗᵢ ⁻¹' T) :=
    hpre.isCompact_closure.totallyBounded.subset subset_closure
  have himg : V.subtypeₗᵢ '' (V.subtypeₗᵢ ⁻¹' T) = T := by
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hrange]
  rw [← himg]
  exact htb.image V.subtypeₗᵢ.isometry.uniformContinuous

namespace MeasureTheory

/-! ### Finite-measure Cauchy-Schwarz bound -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- **Finite-measure Cauchy-Schwarz with one constant factor.** For a set of finite measure,
the square of the integral of `f` is at most `μ.real s` times the integral of `f ^ 2`. This is
the general-measure analogue of `MeasureTheory.sq_intervalIntegral_le`. -/
theorem sq_setIntegral_le (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) {f : α → ℝ}
    (hf : IntegrableOn f s μ) (hf2 : IntegrableOn (fun x => (f x) ^ 2) s μ) :
    (∫ x in s, f x ∂μ) ^ 2 ≤ (μ.real s) * ∫ x in s, (f x) ^ 2 ∂μ := by
  have key : ∀ lam : ℝ,
      0 ≤ (μ.real s) * (lam * lam) + (-2 * ∫ x in s, f x ∂μ) * lam + ∫ x in s, (f x) ^ 2 ∂μ := by
    intro lam
    have hnn : 0 ≤ ∫ x in s, (f x - lam) ^ 2 ∂μ :=
      setIntegral_nonneg hs (fun x _ => by positivity)
    have i2 : IntegrableOn (fun x => (-(2 * lam)) * f x) s μ := hf.const_mul _
    have i12 : IntegrableOn (fun x => (f x) ^ 2 + (-(2 * lam)) * f x) s μ := hf2.add i2
    have i3 : IntegrableOn (fun _ : α => lam ^ 2) s μ := integrableOn_const hμs
    have hexp : ∫ x in s, (f x - lam) ^ 2 ∂μ
        = (μ.real s) * (lam * lam) + (-2 * ∫ x in s, f x ∂μ) * lam + ∫ x in s, (f x) ^ 2 ∂μ := by
      calc ∫ x in s, (f x - lam) ^ 2 ∂μ
          = ∫ x in s, ((f x) ^ 2 + (-(2 * lam)) * f x + lam ^ 2) ∂μ := by
            refine integral_congr_ae ?_; filter_upwards with x; ring
        _ = (∫ x in s, ((f x) ^ 2 + (-(2 * lam)) * f x) ∂μ) + (∫ _x in s, lam ^ 2 ∂μ) :=
            integral_add i12 i3
        _ = ((∫ x in s, (f x) ^ 2 ∂μ) + (∫ x in s, (-(2 * lam)) * f x ∂μ))
              + (∫ _x in s, lam ^ 2 ∂μ) := by rw [integral_add hf2 i2]
        _ = (μ.real s) * (lam * lam) + (-2 * ∫ x in s, f x ∂μ) * lam + ∫ x in s, (f x) ^ 2 ∂μ := by
            rw [integral_const_mul, setIntegral_const, smul_eq_mul]; ring
    rw [← hexp]; exact hnn
  have hdisc := discrim_le_zero key
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-! ### `L²` space, translation, and the squared norm as an integral -/

/-- `L²(ℝⁿ)` with Lebesgue measure. -/
abbrev EucL2 (n : ℕ) := Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))

variable {n : ℕ}

/-- The squared `L²` norm is the integral of the square. -/
theorem norm_sq_eq_integral_sq (g : EucL2 n) : ‖g‖ ^ 2 = ∫ x, (g x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [pow_two]

/-- Translation by `h` as a linear isometry of `L²(ℝⁿ)`. -/
def transL2 (h : EuclideanSpace ℝ (Fin n)) : EucL2 n →ₗᵢ[ℝ] EucL2 n :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (· + h) (measurePreserving_add_right volume h)

/-- A translate is represented almost everywhere by the shifted function. -/
theorem coeFn_transL2 (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    (transL2 h g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => g (x + h) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- The squared `L²` norm of a translation difference, as an integral. -/
theorem norm_sq_transL2_sub (h : EuclideanSpace ℝ (Fin n)) (g : EucL2 n) :
    ‖transL2 h g - g‖ ^ 2 = ∫ x, (g (x + h) - g x) ^ 2 := by
  have hnorm : ‖transL2 h g - g‖ ^ 2 = ∫ x, ((transL2 h g - g) x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    simp_rw [pow_two]
  rw [hnorm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (transL2 h g) g, coeFn_transL2 h g] with x hx hx1
  rw [hx]; simp only [Pi.sub_apply]; rw [hx1]

/-! ### Cube grid -/

/-- The half-open cube of side `η` at lattice index `k`, as a subset of
`EuclideanSpace ℝ (Fin n)`. -/
def cube (η : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun i => Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1)))

/-- Membership of a cube is coordinatewise membership of the defining half-open intervals. -/
theorem mem_cube {η : ℝ} {k : Fin n → ℤ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ cube η k ↔ ∀ i, x i ∈ Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1)) := by
  simp only [cube, mem_preimage, Set.mem_univ_pi]

/-- Every cube is measurable. -/
theorem measurableSet_cube (η : ℝ) (k : Fin n → ℤ) : MeasurableSet (cube η k) :=
  (PiLp.volume_preserving_ofLp (ι := Fin n)).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

/-- A cube of side `η` has volume `η ^ n`, independently of the lattice index. -/
theorem volume_cube (η : ℝ) (k : Fin n → ℤ) :
    volume (cube η k) = (ENNReal.ofReal η) ^ n := by
  have hbox : volume (Set.univ.pi (fun i => Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1))))
      = (ENNReal.ofReal η) ^ n := by
    rw [volume_pi_pi]
    have hone : ∀ i : Fin n,
        volume (Set.Ico (η * (k i : ℝ)) (η * ((k i : ℝ) + 1))) = ENNReal.ofReal η := by
      intro i; rw [Real.volume_Ico]; congr 1; ring
    rw [Finset.prod_congr rfl (fun i _ => hone i)]; simp
  rw [cube, (PiLp.volume_preserving_ofLp (ι := Fin n)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, hbox]

/-- A cube has finite volume, the form the integration lemmas take as a hypothesis. -/
theorem volume_cube_ne_top (η : ℝ) (k : Fin n → ℤ) :
    volume (cube η k) ≠ ⊤ := by
  rw [volume_cube]; exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne

/-- The volume of a cube of nonnegative side, read as a real number. -/
theorem volume_real_cube {η : ℝ} (hη : 0 ≤ η) (k : Fin n → ℤ) :
    volume.real (cube η k) = η ^ n := by
  rw [Measure.real, volume_cube, ENNReal.toReal_pow, ENNReal.toReal_ofReal hη]

/-- Cubes at distinct lattice indices are disjoint. -/
theorem cube_disjoint {η : ℝ} (hη : 0 < η) {k k' : Fin n → ℤ} (hk : k ≠ k') :
    Disjoint (cube η k) (cube η k') := by
  rw [Set.disjoint_left]
  rintro x hx hx'
  apply hk
  funext i
  rw [mem_cube] at hx hx'
  obtain ⟨hl, hu⟩ := hx i
  obtain ⟨hl', hu'⟩ := hx' i
  have c1 : η * (k i : ℝ) < η * ((k' i : ℝ) + 1) := lt_of_le_of_lt hl hu'
  have c2 : η * (k' i : ℝ) < η * ((k i : ℝ) + 1) := lt_of_le_of_lt hl' hu
  have d1 : (k i : ℝ) < (k' i : ℝ) + 1 := lt_of_mul_lt_mul_left c1 hη.le
  have d2 : (k' i : ℝ) < (k i : ℝ) + 1 := lt_of_mul_lt_mul_left c2 hη.le
  have e1 : k i < k' i + 1 := by exact_mod_cast d1
  have e2 : k' i < k i + 1 := by exact_mod_cast d2
  omega

/-- Two points of a common cube differ by less than `η` in each coordinate. -/
theorem coord_dist_lt_of_mem_cube {η : ℝ} {k : Fin n → ℤ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ cube η k) (hy : y ∈ cube η k) (i : Fin n) : |x i - y i| < η := by
  rw [mem_cube] at hx hy
  obtain ⟨hl, hu⟩ := hx i
  obtain ⟨hl', hu'⟩ := hy i
  rw [abs_lt]; constructor <;> linarith

/-! ### Displacement box -/

/-- The open displacement box `(-η, η)ⁿ` in `EuclideanSpace ℝ (Fin n)`: the set of admissible
differences of two points sharing a side-`η` cube. -/
def dbox (η : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun _ => Set.Ioo (-η) η)

/-- Membership of the displacement box is coordinatewise membership of `(-η, η)`. -/
theorem mem_dbox {η : ℝ} {w : EuclideanSpace ℝ (Fin n)} :
    w ∈ dbox η ↔ ∀ i, w i ∈ Set.Ioo (-η) η := by
  simp only [dbox, mem_preimage, Set.mem_univ_pi]

/-- The displacement box is measurable. -/
theorem measurableSet_dbox (η : ℝ) : MeasurableSet (dbox η : Set (EuclideanSpace ℝ (Fin n))) :=
  (PiLp.volume_preserving_ofLp (ι := Fin n)).measurable
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)

/-- The displacement box of half-width `η` has volume `(2 η) ^ n`. -/
theorem volume_dbox (η : ℝ) :
    volume (dbox η : Set (EuclideanSpace ℝ (Fin n))) = (ENNReal.ofReal (2 * η)) ^ n := by
  have hbox : volume (Set.univ.pi (fun _ : Fin n => Set.Ioo (-η) η))
      = (ENNReal.ofReal (2 * η)) ^ n := by
    rw [volume_pi_pi]
    have hone : ∀ i : Fin n, volume (Set.Ioo (-η) η) = ENNReal.ofReal (2 * η) := by
      intro i; rw [Real.volume_Ioo]; congr 1; ring
    rw [Finset.prod_congr rfl (fun i _ => hone i)]; simp
  rw [dbox, (PiLp.volume_preserving_ofLp (ι := Fin n)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, hbox]

/-- The displacement box has finite volume, the form the integration lemmas take as a
hypothesis. -/
theorem volume_dbox_ne_top (η : ℝ) :
    volume (dbox η : Set (EuclideanSpace ℝ (Fin n))) ≠ ⊤ := by
  rw [volume_dbox]; exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne

/-- The volume of the displacement box of nonnegative half-width, read as a real number. -/
theorem volume_real_dbox {η : ℝ} (hη : 0 ≤ η) :
    volume.real (dbox η : Set (EuclideanSpace ℝ (Fin n))) = (2 * η) ^ n := by
  rw [Measure.real, volume_dbox, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]

/-- The coordinate difference of two points in a common cube lies in the displacement box. -/
theorem sub_mem_dbox_of_mem_cube {η : ℝ} {k : Fin n → ℤ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ cube η k) (hy : y ∈ cube η k) : y - x ∈ dbox η := by
  rw [mem_dbox]
  intro i
  have h := coord_dist_lt_of_mem_cube hx hy i
  rw [abs_lt] at h
  simp only [Set.mem_Ioo, PiLp.sub_apply]
  constructor <;> linarith [h.1, h.2]

/-- A point of the displacement box has squared norm at most `n * η ^ 2`. -/
theorem normSq_le_of_mem_dbox {η : ℝ} {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ dbox η) :
    ‖w‖ ^ 2 ≤ n * η ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  rw [mem_dbox] at hw
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin n, η ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        obtain ⟨hl, hu⟩ := hw i
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [hl, hu]
    _ = n * η ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Cube-averaging operator -/

/-- The `L²` class of the indicator of the cube `cube η k`. -/
def cubeIndicator (η : ℝ) (k : Fin n → ℤ) : EucL2 n :=
  indicatorConstLp 2 (measurableSet_cube η k) (volume_cube_ne_top η k) (1 : ℝ)

/-- The average value of `g` over the cube `cube η k`. -/
def cubeCoef (η : ℝ) (k : Fin n → ℤ) (g : EucL2 n) : ℝ :=
  (volume.real (cube η k))⁻¹ * ∫ x in cube η k, g x

/-- The cube-averaging operator: the piecewise-constant approximation of `g` on the grid of
side-`η` cubes indexed by `K`, as an element of `L²`. -/
def avg (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) : EucL2 n :=
  ∑ k ∈ K, cubeCoef η k g • cubeIndicator η k

/-- The averaging operator as a pointwise piecewise-constant function. -/
def stepFun (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ∑ k ∈ K, cubeCoef η k g * (cube η k).indicator (fun _ => (1 : ℝ)) x

/-- The coercion of a finite `L²` sum is almost everywhere the pointwise sum. -/
theorem coeFn_lp_sum {ι : Type*} (s : Finset ι) (F : ι → EucL2 n) :
    (⇑(∑ i ∈ s, F i) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 volume
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hx hx2
    rw [hx]; simp only [Pi.add_apply]; rw [hx2, Finset.sum_insert hi]

/-- The averaging operator agrees almost everywhere with its piecewise-constant representative. -/
theorem coeFn_avg (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    (avg η K g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] stepFun η K g := by
  refine (coeFn_lp_sum K _).trans ?_
  have hterm : ∀ k ∈ K, (⇑(cubeCoef η k g • cubeIndicator η k) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun x => cubeCoef η k g * (cube η k).indicator (fun _ => (1 : ℝ)) x := by
    intro k _
    filter_upwards [Lp.coeFn_smul (cubeCoef η k g) (cubeIndicator η k),
      indicatorConstLp_coeFn (p := 2) (μ := volume) (hs := measurableSet_cube η k)
        (hμs := volume_cube_ne_top η k) (c := (1 : ℝ))] with x hx hx2
    rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (cubeIndicator η k) x = (cube η k).indicator (fun _ => (1 : ℝ)) x from hx2]
  filter_upwards [(eventually_all_finset K).mpr hterm] with x hx
  exact Finset.sum_congr rfl (fun k hk => hx k hk)

/-- The averaging operator lands in the finite-dimensional span of the cube indicators. -/
theorem avg_mem_span (η : ℝ) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    avg η K g ∈ Submodule.span ℝ (cubeIndicator η '' (K : Set (Fin n → ℤ))) := by
  refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨k, hk, rfl⟩

/-- On a cube of the grid, the piecewise-constant representative equals that cube's average. -/
theorem stepFun_eq_on_cube {η : ℝ} (hη : 0 < η) {K : Finset (Fin n → ℤ)} {g : EucL2 n}
    {k₀ : Fin n → ℤ} (hk₀ : k₀ ∈ K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube η k₀) :
    stepFun η K g x = cubeCoef η k₀ g := by
  unfold stepFun
  rw [Finset.sum_eq_single k₀]
  · rw [Set.indicator_of_mem hx]; ring
  · intro k _ hne
    rw [Set.indicator_of_notMem
      (fun hxk => absurd hx (Set.disjoint_left.mp (cube_disjoint hη hne) hxk)), mul_zero]
  · intro h; exact absurd hk₀ h

/-! ### Approximation error as a sum of cube variances -/

/-- On any cube the squared deviation of `g` from a constant is integrable. -/
theorem integrableOn_cube_sq_sub (η : ℝ) (k : Fin n → ℤ) (g : EucL2 n) (c : ℝ) :
    IntegrableOn (fun y => (g y - c) ^ 2) (cube η k) volume := by
  have : IsFiniteMeasure (volume.restrict (cube η k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (volume_cube_ne_top η k).lt_top⟩
  have hg2 : MemLp (fun y => (g : EuclideanSpace ℝ (Fin n) → ℝ) y) 2
      (volume.restrict (cube η k)) := (Lp.memLp g).restrict (cube η k)
  have hc2 : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => c) 2 (volume.restrict (cube η k)) :=
    memLp_const c
  exact (hg2.sub hc2).integrable_sq

/-- **Approximation error as a sum of cube variances.** When `g` is supported in
the union of the grid cubes, the squared `L²` distance from `g` to its cube-average is the sum
over cubes of the squared deviation of `g` from its average on that cube. -/
theorem norm_sq_sub_avg_eq {η : ℝ} (hη : 0 < η) {K : Finset (Fin n → ℤ)} {g : EucL2 n}
    (hsupp : ∀ᵐ x ∂volume, x ∉ (⋃ k ∈ K, cube η k) → g x = 0) :
    ‖g - avg η K g‖ ^ 2 = ∑ k ∈ K, ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2 := by
  rw [norm_sq_eq_integral_sq]
  have hae : (fun x => ((g - avg η K g) x) ^ 2) =ᵐ[volume]
      fun x => ∑ k ∈ K, (cube η k).indicator (fun y => (g y - cubeCoef η k g) ^ 2) x := by
    filter_upwards [Lp.coeFn_sub g (avg η K g), coeFn_avg η K g, hsupp] with x hsub havg hsup
    rw [hsub]; simp only [Pi.sub_apply]; rw [havg]
    by_cases hmem : x ∈ ⋃ k ∈ K, cube η k
    · obtain ⟨k₀, hk₀K, hk₀⟩ := Set.mem_iUnion₂.mp hmem
      rw [stepFun_eq_on_cube hη hk₀K hk₀,
        Finset.sum_eq_single k₀
          (fun k _ hne => Set.indicator_of_notMem
            (fun hxk => absurd hk₀ (Set.disjoint_left.mp (cube_disjoint hη hne) hxk)) _)
          (fun h => absurd hk₀K h),
        Set.indicator_of_mem hk₀]
    · rw [hsup hmem]
      have hstep0 : stepFun η K g x = 0 :=
        Finset.sum_eq_zero (fun k hk => by
          rw [Set.indicator_of_notMem (fun hxk => hmem (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)),
            mul_zero])
      have hsum0 : (∑ k ∈ K, (cube η k).indicator (fun y => (g y - cubeCoef η k g) ^ 2) x) = 0 :=
        Finset.sum_eq_zero (fun k hk => Set.indicator_of_notMem
          (fun hxk => hmem (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)) _)
      rw [hstep0, hsum0]; norm_num
  rw [integral_congr_ae hae,
    integral_finsetSum K (fun k _ => (integrable_indicator_iff (measurableSet_cube η k)).mpr
      (integrableOn_cube_sq_sub η k g _))]
  exact Finset.sum_congr rfl (fun k _ => integral_indicator (measurableSet_cube η k))

/-! ### Cube-translation estimate -/

/-- The squared difference `(g x - g y) ^ 2` is integrable over a product of finite-measure sets. -/
theorem integrableOn_prod_sq_sub (g : EucL2 n) {s t : Set (EuclideanSpace ℝ (Fin n))}
    (hμs : volume s ≠ ⊤) (hμt : volume t ≠ ⊤) :
    IntegrableOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (g p.1 - g p.2) ^ 2) (s ×ˢ t) (volume.prod volume) := by
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμs.lt_top⟩
  have : IsFiniteMeasure (volume.restrict t) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμt.lt_top⟩
  rw [IntegrableOn, ← Measure.prod_restrict]
  have hgs : AEStronglyMeasurable (g : EuclideanSpace ℝ (Fin n) → ℝ) (volume.restrict s) :=
    (Lp.aestronglyMeasurable g).restrict
  have hgt : AEStronglyMeasurable (g : EuclideanSpace ℝ (Fin n) → ℝ) (volume.restrict t) :=
    (Lp.aestronglyMeasurable g).restrict
  have hmeas : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (g p.1 - g p.2) ^ 2) ((volume.restrict s).prod (volume.restrict t)) :=
    ((hgs.comp_fst (ν := volume.restrict t)).sub (hgt.comp_snd (μ := volume.restrict s))).pow 2
  have hg2s : Integrable (fun x => (g x) ^ 2) (volume.restrict s) :=
    ((Lp.memLp g).restrict s).integrable_sq
  have hg2t : Integrable (fun y => (g y) ^ 2) (volume.restrict t) :=
    ((Lp.memLp g).restrict t).integrable_sq
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      2 * (g p.1) ^ 2 + 2 * (g p.2) ^ 2) ((volume.restrict s).prod (volume.restrict t)) :=
    ((hg2s.comp_fst (volume.restrict t)).const_mul 2).add
      ((hg2t.comp_snd (volume.restrict s)).const_mul 2)
  refine hdom.mono' hmeas ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (g p.1 - g p.2), sq_nonneg (g p.1 + g p.2)]

/-- **Displacement product integrability.** The squared difference `(g x - g (x + w)) ^ 2`
is integrable over `ℝⁿ × D` for any finite-measure `D` of displacements. This is what admits the
Tonelli swap in the cube-translation estimate: the `w`-marginal of the integrand is the constant
`‖g‖ ^ 2` (translation is an `L²` isometry), so `integrable_prod_iff'` closes. -/
theorem integrable_prod_displacement (g : EucL2 n) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hμD : volume D ≠ ⊤) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (g p.1 - g (p.1 + p.2)) ^ 2) (volume.prod (volume.restrict D)) := by
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμD.lt_top⟩
  have hshear : MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (p.1, p.1 + p.2))
      (volume.prod volume) (volume.prod volume) :=
    measurePreserving_prod_add (μ := volume) (ν := volume)
  have h1 : AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => g q.2) (volume.prod volume) :=
    (Lp.aestronglyMeasurable g).comp_snd (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hmeas_shear : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (p.1, p.1 + p.2)) := by
    fun_prop
  have haesm_add0 : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => g (p.1 + p.2))
      (volume.prod volume) := by
    have hg' : AEStronglyMeasurable
        (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => g q.2)
        (Measure.map (fun p => (p.1, p.1 + p.2)) (volume.prod volume)) := by
      rw [hshear.map_eq]; exact h1
    exact hg'.comp_measurable hmeas_shear
  have heqμ : volume.prod (volume.restrict D)
      = (volume.prod (volume : Measure (EuclideanSpace ℝ (Fin n)))).restrict
        ((Set.univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ D) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have haesm_add : AEStronglyMeasurable (fun p => g (p.1 + p.2))
      (volume.prod (volume.restrict D)) := by
    rw [heqμ]; exact haesm_add0.restrict
  have hmeas : AEStronglyMeasurable (fun p => (g p.1 - g (p.1 + p.2)) ^ 2)
      (volume.prod (volume.restrict D)) :=
    (((Lp.aestronglyMeasurable g).comp_fst (ν := volume.restrict D)).sub haesm_add).pow 2
  have hI1 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (g p.1) ^ 2)
      (volume.prod (volume.restrict D)) :=
    (MemLp.integrable_sq (Lp.memLp g)).comp_fst (volume.restrict D)
  have haesm_sq : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (g (p.1 + p.2)) ^ 2)
      (volume.prod (volume.restrict D)) := haesm_add.pow 2
  have hI2 : Integrable (fun p => (g (p.1 + p.2)) ^ 2) (volume.prod (volume.restrict D)) := by
    refine (integrable_prod_iff' haesm_sq).mpr ⟨Filter.Eventually.of_forall (fun w => ?_), ?_⟩
    · simp only
      have hcoe : (transL2 w g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => g (x + w) :=
        coeFn_transL2 w g
      exact ((Lp.memLp (transL2 w g)).integrable_sq).congr
        (by filter_upwards [hcoe] with x hx; rw [hx])
    · have hmargfun : (fun w => ∫ x, ‖(g (x + w)) ^ 2‖)
          = (fun _ : EuclideanSpace ℝ (Fin n) => ‖g‖ ^ 2) := by
        funext w
        have hnorm : ∫ x, ‖(g (x + w)) ^ 2‖ = ∫ x, (g (x + w)) ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (sq_nonneg _))
        rw [hnorm]
        have hcoe : (transL2 w g : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => g (x + w) :=
          coeFn_transL2 w g
        calc ∫ x, (g (x + w)) ^ 2 = ∫ x, ((transL2 w g) x) ^ 2 := by
              refine integral_congr_ae ?_; filter_upwards [hcoe] with x hx; rw [hx]
          _ = ‖transL2 w g‖ ^ 2 := (norm_sq_eq_integral_sq _).symm
          _ = ‖g‖ ^ 2 := by rw [(transL2 w).norm_map]
      simp only
      rw [hmargfun]; exact integrableOn_const (C := ‖g‖ ^ 2) hμD
  refine ((hI1.const_mul 2).add (hI2.const_mul 2)).mono' hmeas ?_
  filter_upwards with p
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (g p.1 - g (p.1 + p.2)), sq_nonneg (g p.1 + g (p.1 + p.2))]

/-- The squared difference of `g` at `x` and `x + w` is integrable over the displacement box. -/
theorem integrableOn_dbox_sq_sub_translate {η : ℝ} (g : EucL2 n) (x : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun w => (g x - g (x + w)) ^ 2) (dbox η) volume := by
  have : IsFiniteMeasure (volume.restrict (dbox η : Set (EuclideanSpace ℝ (Fin n)))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (volume_dbox_ne_top (n := n) η).lt_top⟩
  have hmp : MeasurePreserving (fun w => x + w)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) volume :=
    measurePreserving_add_left volume x
  have hemb : MeasurableEmbedding (fun w : EuclideanSpace ℝ (Fin n) => x + w) :=
    (MeasurableEquiv.addLeft x).measurableEmbedding
  have hgxw2 : IntegrableOn (fun w => (g (x + w)) ^ 2) (dbox η) volume :=
    ((hmp.integrable_comp_emb hemb).mpr (MemLp.integrable_sq (Lp.memLp g))).integrableOn
  have haesm_gxw : AEStronglyMeasurable (fun w => g (x + w)) (volume.restrict (dbox η)) := by
    have hmap : AEStronglyMeasurable (g : EuclideanSpace ℝ (Fin n) → ℝ)
        (Measure.map (fun w => x + w) volume) := by rw [hmp.map_eq]; exact Lp.aestronglyMeasurable g
    exact (hmap.comp_measurable (by fun_prop)).restrict
  have haesm : AEStronglyMeasurable (fun w => (g x - g (x + w)) ^ 2) (volume.restrict (dbox η)) :=
    (aestronglyMeasurable_const.sub haesm_gxw).pow 2
  have hdom : Integrable (fun w => 2 * (g x) ^ 2 + 2 * (g (x + w)) ^ 2)
      (volume.restrict (dbox η)) :=
    ((integrableOn_const (C := (g x) ^ 2) (volume_dbox_ne_top (n := n) η)).const_mul 2).add
      (hgxw2.const_mul 2)
  refine hdom.mono' haesm ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (g x - g (x + w)), sq_nonneg (g x + g (x + w))]

/-- **Displacement substitution.** On a cube the integral of the squared difference is at most the
integral of the squared translation difference over the displacement box. -/
theorem inner_displacement_le {η : ℝ} (k : Fin n → ℤ) (g : EucL2 n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube η k) :
    ∫ y in cube η k, (g x - g y) ^ 2 ≤ ∫ w in dbox η, (g x - g (x + w)) ^ 2 := by
  have hmp : MeasurePreserving (fun w => x + w)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) volume :=
    measurePreserving_add_left volume x
  have hemb : MeasurableEmbedding (fun w : EuclideanSpace ℝ (Fin n) => x + w) :=
    (MeasurableEquiv.addLeft x).measurableEmbedding
  have hsub : ∫ y in cube η k, (g x - g y) ^ 2
      = ∫ w in (fun w => x + w) ⁻¹' (cube η k), (g x - g (x + w)) ^ 2 :=
    (hmp.setIntegral_preimage_emb hemb (fun y => (g x - g y) ^ 2) (cube η k)).symm
  rw [hsub]
  have hPsub : (fun w => x + w) ⁻¹' (cube η k) ⊆ dbox η := by
    intro w hw
    have hmem : x + w ∈ cube η k := hw
    have hd := sub_mem_dbox_of_mem_cube hx hmem
    simpa using hd
  exact setIntegral_mono_set (integrableOn_dbox_sq_sub_translate g x)
    (Filter.Eventually.of_forall fun w => sq_nonneg _)
    (Filter.Eventually.of_forall fun w hw => hPsub hw)

/-- **Tonelli marginal.** Swapping the order of integration turns the displacement integral into
the translation modulus integrated over the displacement set. -/
theorem integral_displacement_marginal (g : EucL2 n) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : MeasurableSet D) (hμD : volume D ≠ ⊤) :
    ∫ x, ∫ w in D, (g x - g (x + w)) ^ 2 = ∫ w in D, ‖transL2 w g - g‖ ^ 2 := by
  rw [integral_integral_swap (integrable_prod_displacement g hμD)]
  refine setIntegral_congr_fun hD (fun w _ => ?_)
  rw [norm_sq_transL2_sub]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- **Cube-translation bound.** Summing the per-cube double integrals over the grid is
controlled by the translation modulus integrated over the displacement box. -/
theorem sum_cube_double_le_translation {η : ℝ} (hη : 0 < η) (K : Finset (Fin n → ℤ)) (g : EucL2 n) :
    ∑ k ∈ K, ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2
      ≤ ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 := by
  set Hfun : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ∫ w in dbox η, (g x - g (x + w)) ^ 2 with hHfun
  have hHint : Integrable Hfun volume :=
    (integrable_prod_displacement g (volume_dbox_ne_top η)).integral_prod_left
  have hHnn : ∀ x, 0 ≤ Hfun x := fun x => integral_nonneg (fun w => sq_nonneg _)
  have step1 : ∑ k ∈ K, ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2
      ≤ ∑ k ∈ K, ∫ x in cube η k, Hfun x := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hFinner : IntegrableOn (fun x => ∫ y in cube η k, (g x - g y) ^ 2) (cube η k) volume := by
      have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (g p.1 - g p.2) ^ 2)
          ((volume.restrict (cube η k)).prod (volume.restrict (cube η k))) := by
        rw [Measure.prod_restrict]
        exact integrableOn_prod_sq_sub g (volume_cube_ne_top η k) (volume_cube_ne_top η k)
      exact hprod.integral_prod_left
    exact setIntegral_mono_on hFinner hHint.integrableOn (measurableSet_cube η k)
      (fun x hx => inner_displacement_le k g hx)
  have step2 : ∑ k ∈ K, ∫ x in cube η k, Hfun x ≤ ∫ x, Hfun x := by
    have heq : ∑ k ∈ K, ∫ x in cube η k, Hfun x = ∫ x, ∑ k ∈ K, (cube η k).indicator Hfun x := by
      rw [integral_finsetSum K (fun k _ => (integrable_indicator_iff (measurableSet_cube η k)).mpr
        hHint.integrableOn)]
      exact Finset.sum_congr rfl (fun k _ => (integral_indicator (measurableSet_cube η k)).symm)
    rw [heq]
    refine integral_mono (integrable_finsetSum K (fun k _ =>
      (integrable_indicator_iff (measurableSet_cube η k)).mpr hHint.integrableOn))
      hHint (fun x => ?_)
    by_cases hx : ∃ k ∈ K, x ∈ cube η k
    · obtain ⟨k₀, hk₀, hx₀⟩ := hx
      refine le_of_eq ?_
      rw [Finset.sum_eq_single k₀
        (fun k _ hne => Set.indicator_of_notMem
          (fun hxk => absurd hx₀ (Set.disjoint_left.mp (cube_disjoint hη hne) hxk)) _)
        (fun h => absurd hk₀ h), Set.indicator_of_mem hx₀]
    · simp only [not_exists, not_and] at hx
      rw [Finset.sum_eq_zero (fun k hk => Set.indicator_of_notMem (hx k hk) _)]
      exact hHnn x
  calc ∑ k ∈ K, ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2
      ≤ ∫ x, Hfun x := step1.trans step2
    _ = ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 :=
        integral_displacement_marginal g (measurableSet_dbox η) (volume_dbox_ne_top η)

/-- **Per-cube variance bound (Jensen).** The squared deviation of `g` from its average on a cube
is at most the rescaled double integral of the squared difference over that cube. -/
theorem cube_variance_le {η : ℝ} (hη : 0 < η) (k : Fin n → ℤ) (g : EucL2 n) :
    ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2
      ≤ (η ^ n)⁻¹ * ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2 := by
  have hηn : (0 : ℝ) < η ^ n := pow_pos hη n
  have hne : (η : ℝ) ^ n ≠ 0 := hηn.ne'
  have hμreal : volume.real (cube η k) = η ^ n := volume_real_cube hη.le k
  have hμne : volume (cube η k) ≠ ⊤ := volume_cube_ne_top η k
  have hgint : IntegrableOn (g : EuclideanSpace ℝ (Fin n) → ℝ) (cube η k) volume :=
    integrableOn_Lp_of_measure_ne_top g (by norm_num) hμne
  have hmarg : IntegrableOn (fun x => ∫ y in cube η k, (g x - g y) ^ 2) (cube η k) volume := by
    have hprod : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (g p.1 - g p.2) ^ 2)
        ((volume.restrict (cube η k)).prod (volume.restrict (cube η k))) := by
      rw [Measure.prod_restrict]; exact integrableOn_prod_sq_sub g hμne hμne
    exact hprod.integral_prod_left
  have hpt_eq : ∀ x, (g x - cubeCoef η k g) = (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) := by
    intro x
    have hI : ∫ y in cube η k, (g x - g y) = (η ^ n) * g x - ∫ y in cube η k, g y := by
      rw [integral_sub (integrableOn_const (C := g x) hμne) hgint, setIntegral_const, smul_eq_mul,
        hμreal]
    rw [hI, cubeCoef, hμreal]; field_simp
  have hpt_le : ∀ x ∈ cube η k,
      (g x - cubeCoef η k g) ^ 2 ≤ (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) ^ 2 := by
    intro x _
    have hsqint : IntegrableOn (fun y => (g x - g y) ^ 2) (cube η k) volume := by
      have heq : (fun y => (g x - g y) ^ 2)
          = (fun y => ((g : EuclideanSpace ℝ (Fin n) → ℝ) y - g x) ^ 2) := by funext y; ring
      rw [heq]; exact integrableOn_cube_sq_sub η k g (g x)
    have hcs : (∫ y in cube η k, (g x - g y)) ^ 2 ≤ (η ^ n) * ∫ y in cube η k, (g x - g y) ^ 2 := by
      have := sq_setIntegral_le (measurableSet_cube η k) hμne
        ((integrableOn_const (C := g x) hμne).sub hgint) hsqint
      rwa [hμreal] at this
    rw [hpt_eq x, mul_pow]
    calc ((η ^ n)⁻¹) ^ 2 * (∫ y in cube η k, (g x - g y)) ^ 2
        ≤ ((η ^ n)⁻¹) ^ 2 * ((η ^ n) * ∫ y in cube η k, (g x - g y) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) ^ 2 := by rw [sq]; field_simp
  calc ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2
      ≤ ∫ x in cube η k, (η ^ n)⁻¹ * ∫ y in cube η k, (g x - g y) ^ 2 :=
        setIntegral_mono_on (integrableOn_cube_sq_sub η k g _) (hmarg.const_mul _)
          (measurableSet_cube η k) hpt_le
    _ = (η ^ n)⁻¹ * ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2 := by
        rw [integral_const_mul]

/-- **Uniform approximation estimate.** For `g` supported in the union of the grid cubes, the
squared `L²` distance from `g` to its cube-average is controlled by the translation modulus over the
displacement box. -/
theorem norm_sq_sub_avg_le_translation {η : ℝ} (hη : 0 < η) {K : Finset (Fin n → ℤ)} {g : EucL2 n}
    (hsupp : ∀ᵐ x ∂volume, x ∉ (⋃ k ∈ K, cube η k) → g x = 0) :
    ‖g - avg η K g‖ ^ 2 ≤ (η ^ n)⁻¹ * ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 := by
  rw [norm_sq_sub_avg_eq hη hsupp]
  calc ∑ k ∈ K, ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2
      ≤ ∑ k ∈ K, (η ^ n)⁻¹ * ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2 :=
        Finset.sum_le_sum (fun k _ => cube_variance_le hη k g)
    _ = (η ^ n)⁻¹ * ∑ k ∈ K, ∫ x in cube η k, ∫ y in cube η k, (g x - g y) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (η ^ n)⁻¹ * ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_cube_double_le_translation hη K g)
          (inv_nonneg.mpr (pow_nonneg hη.le n))

/-- The translation modulus is integrable over the displacement box. -/
theorem integrableOn_dbox_translation_modulus {η : ℝ} (g : EucL2 n) :
    IntegrableOn (fun w => ‖transL2 w g - g‖ ^ 2) (dbox η) volume := by
  refine ((integrable_prod_displacement g (volume_dbox_ne_top η)).integral_prod_right).congr ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  change ∫ x, ((g : EuclideanSpace ℝ (Fin n) → ℝ) x - g (x + w)) ^ 2 = ‖transL2 w g - g‖ ^ 2
  rw [norm_sq_transL2_sub]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- **Constant approximation bound.** With a uniform Lipschitz translation modulus `Λ`, the
cube-average approximates `g` within `2 ^ n * n * Λ ^ 2 * η ^ 2` in squared `L²` norm. -/
theorem norm_sq_sub_avg_le_const {η : ℝ} (hη : 0 < η) {K : Finset (Fin n → ℤ)} {g : EucL2 n}
    {Λ : ℝ}
    (hsupp : ∀ᵐ x ∂volume, x ∉ (⋃ k ∈ K, cube η k) → g x = 0)
    (hmod : ∀ h, ‖transL2 h g - g‖ ≤ Λ * ‖h‖) :
    ‖g - avg η K g‖ ^ 2 ≤ 2 ^ n * n * Λ ^ 2 * η ^ 2 := by
  have hne : (η : ℝ) ^ n ≠ 0 := (pow_pos hη n).ne'
  have hbound : ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 ≤ (2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2)) := by
    have hpt : ∀ w ∈ dbox η, ‖transL2 w g - g‖ ^ 2 ≤ Λ ^ 2 * (n * η ^ 2) := by
      intro w hw
      have h1 : ‖transL2 w g - g‖ ^ 2 ≤ (Λ * ‖w‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hmod w) 2
      have h2 : ‖w‖ ^ 2 ≤ n * η ^ 2 := normSq_le_of_mem_dbox hw
      nlinarith [norm_nonneg w, normSq_le_of_mem_dbox hw, sq_nonneg Λ]
    calc ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2
        ≤ ∫ _w in dbox η, Λ ^ 2 * (n * η ^ 2) :=
          setIntegral_mono_on (integrableOn_dbox_translation_modulus g)
            (integrableOn_const (volume_dbox_ne_top η)) (measurableSet_dbox η) hpt
      _ = (2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2)) := by
          rw [setIntegral_const, smul_eq_mul, volume_real_dbox hη.le]
  calc ‖g - avg η K g‖ ^ 2 ≤ (η ^ n)⁻¹ * ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 :=
        norm_sq_sub_avg_le_translation hη hsupp
    _ ≤ (η ^ n)⁻¹ * ((2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2))) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (pow_nonneg hη.le n))
    _ = 2 ^ n * n * Λ ^ 2 * η ^ 2 := by rw [mul_pow]; field_simp

/-! ### Fréchet-Kolmogorov criterion -/

/-- Each coordinate of a Euclidean vector is bounded in absolute value by the norm. -/
theorem coord_abs_le_norm (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : |x i| ≤ ‖x‖ := by
  rw [show |x i| = Real.sqrt ((x i) ^ 2) from (Real.sqrt_sq_eq_abs (x i)).symm,
    EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [show (x i) ^ 2 = ‖x i‖ ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  exact Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

/-- **Coverage.** A closed ball of radius `R` is covered by the finitely many grid cubes of
side `η` whose lattice index lies in a box scaled to `R / η`. -/
theorem closedBall_subset_iUnion_cube {η : ℝ} (hη : 0 < η) (R : ℝ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆
      ⋃ k ∈ Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(⌈R / η⌉ + 1)) (⌈R / η⌉ + 1)),
        cube η k := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  set k : Fin n → ℤ := fun i => ⌊x i / η⌋ with hk
  have hmem : ∀ i, η * (k i : ℝ) ≤ x i ∧ x i < η * ((k i : ℝ) + 1) := by
    intro i
    refine ⟨?_, ?_⟩
    · calc η * (k i : ℝ) ≤ η * (x i / η) :=
            mul_le_mul_of_nonneg_left (Int.floor_le (x i / η)) hη.le
        _ = x i := by field_simp
    · calc x i = η * (x i / η) := by field_simp
        _ < η * ((k i : ℝ) + 1) := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x i / η)) hη
  have hxcube : x ∈ cube η k := by
    rw [mem_cube]; intro i; exact ⟨(hmem i).1, (hmem i).2⟩
  refine Set.mem_biUnion ?_ hxcube
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hxiR : |x i| ≤ R := (coord_abs_le_norm x i).trans hx
  obtain ⟨hxle, hxlt⟩ := hmem i
  have hub : k i ≤ ⌈R / η⌉ := by
    have h1 : (k i : ℝ) ≤ R / η := by
      rw [le_div_iff₀ hη, mul_comm]
      exact hxle.trans (le_trans (le_abs_self (x i)) hxiR)
    have h2 : (k i : ℝ) ≤ (⌈R / η⌉ : ℝ) := h1.trans (Int.le_ceil (R / η))
    exact_mod_cast h2
  have hlb : -(⌈R / η⌉ + 1) ≤ k i := by
    have hge : -R ≤ x i := by linarith [neg_abs_le (x i), hxiR]
    have hRlt : -R < ((k i : ℝ) + 1) * η := by rw [mul_comm]; exact lt_of_le_of_lt hge hxlt
    have h1 : -(R / η) < (k i : ℝ) + 1 := by rw [← neg_div, div_lt_iff₀ hη]; exact hRlt
    have h2 : -((⌈R / η⌉ : ℝ)) ≤ -(R / η) := by linarith [Int.le_ceil (R / η)]
    have h3 : -((⌈R / η⌉ : ℝ)) < (k i : ℝ) + 1 := lt_of_le_of_lt h2 h1
    have h4 : (-(⌈R / η⌉ + 1) : ℝ) < (k i : ℝ) := by linarith
    exact_mod_cast h4.le
  exact ⟨hlb, le_trans hub (by omega)⟩

/-- **Fréchet-Kolmogorov precompactness criterion.** A family `S` of `L²(ℝⁿ)` functions that
is uniformly bounded in norm, uniformly supported in a fixed closed ball, and uniformly Lipschitz
under translation (with modulus `Λ`) is totally bounded. This is the precompactness engine behind
the Rellich-Kondrachov compact embedding. -/
theorem totallyBounded_of_lipschitz_translation (S : Set (EucL2 n)) {R M Λ : ℝ}
    (hbdd : ∀ g ∈ S, ‖g‖ ≤ M)
    (hsupp : ∀ g ∈ S, ∀ᵐ x ∂volume,
      x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R → g x = 0)
    (hmod : ∀ g ∈ S, ∀ h, ‖transL2 h g - g‖ ≤ Λ * ‖h‖) :
    TotallyBounded S := by
  apply totallyBounded_of_approx
  intro ε hε
  set D : ℝ := 2 ^ n * n * Λ ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hden : 0 < Real.sqrt D + 1 := by linarith
  set η : ℝ := ε / (Real.sqrt D + 1) with hη_def
  have hη : 0 < η := div_pos hε hden
  set K : Finset (Fin n → ℤ) :=
    Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(⌈R / η⌉ + 1)) (⌈R / η⌉ + 1)) with hK_def
  have hDη : D * η ^ 2 < ε ^ 2 := by
    have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0
    have hη2 : η ^ 2 * (Real.sqrt D + 1) ^ 2 = ε ^ 2 := by
      rw [hη_def, div_pow]; field_simp
    have key : D * η ^ 2 * (Real.sqrt D + 1) ^ 2 < ε ^ 2 * (Real.sqrt D + 1) ^ 2 :=
      calc D * η ^ 2 * (Real.sqrt D + 1) ^ 2 = D * ε ^ 2 := by rw [mul_assoc, hη2]
        _ < ε ^ 2 * (Real.sqrt D + 1) ^ 2 := by
            nlinarith [hs, mul_nonneg (sq_nonneg ε) hsqrt0, mul_pos hε hε]
    exact lt_of_mul_lt_mul_right key (by positivity)
  have happrox : ∀ g ∈ S, ‖g - avg η K g‖ < ε := by
    intro g hg
    have hsupp' : ∀ᵐ x ∂volume, x ∉ (⋃ k ∈ K, cube η k) → g x = 0 := by
      filter_upwards [hsupp g hg] with x hx
      exact fun hxnc => hx (fun hb => hxnc (closedBall_subset_iUnion_cube hη R hb))
    have hb : ‖g - avg η K g‖ ^ 2 ≤ D * η ^ 2 := by
      rw [hD]; exact norm_sq_sub_avg_le_const hη hsupp' (hmod g hg)
    have hlt : ‖g - avg η K g‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt hb hDη
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  refine ⟨avg η K '' S, ?_, ?_⟩
  · have : FiniteDimensional ℝ (Submodule.span ℝ (cubeIndicator η '' (K : Set (Fin n → ℤ)))) :=
      FiniteDimensional.span_of_finite ℝ (K.finite_toSet.image _)
    refine totallyBounded_of_finiteDimensional_bounded
      (Submodule.span ℝ (cubeIndicator η '' (K : Set (Fin n → ℤ)))) ?_ ?_
    · rintro _ ⟨g, _, rfl⟩; exact avg_mem_span η K g
    · apply (Metric.isBounded_closedBall (x := (0 : EucL2 n)) (r := M + ε)).subset
      rintro _ ⟨g, hg, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have htri : ‖avg η K g‖ ≤ ‖g‖ + ‖g - avg η K g‖ :=
        calc ‖avg η K g‖ = ‖g - (g - avg η K g)‖ := by congr 1; abel
          _ ≤ ‖g‖ + ‖g - avg η K g‖ := norm_sub_le _ _
      linarith [hbdd g hg, (happrox g hg).le]
  · intro g hg
    refine ⟨avg η K g, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_eq_norm]; exact happrox g hg

/-! ### Passing a translation modulus to `L²` limits

The translation modulus that feeds `totallyBounded_of_lipschitz_translation` is closed under `L²`
limits. This is the bridge from `MeasureTheory.integral_sq_sub_translation_le`, which supplies the
estimate for smooth compactly supported functions, to its consequence on the `L²` classes of Sobolev
functions: a Sobolev function is an `L²` limit of smooth compactly supported functions whose
gradients are uniformly bounded, and the modulus passes to the limit. Both the graph-closure `H₀¹`
of the elliptic problem and the `W^{1,p}` structure of the Navier-Stokes development obtain their
modulus through this lemma.
-/

/-- A uniform translation modulus passes to an `L²` limit: if every `gk k` satisfies
`‖transL2 h (gk k) - gk k‖ ≤ Λ * ‖h‖` and `gk` converges to `g`, then `g` satisfies the same
bound. -/
theorem transL2_sub_le_of_tendsto {g : EucL2 n} {Λ : ℝ} {gk : ℕ → EucL2 n}
    (htend : Filter.Tendsto gk Filter.atTop (nhds g))
    (hmod : ∀ k, ∀ h, ‖transL2 h (gk k) - gk k‖ ≤ Λ * ‖h‖)
    (h : EuclideanSpace ℝ (Fin n)) : ‖transL2 h g - g‖ ≤ Λ * ‖h‖ := by
  have hcont : Filter.Tendsto (fun k => transL2 h (gk k) - gk k) Filter.atTop
      (nhds (transL2 h g - g)) :=
    (((transL2 h).continuous.tendsto g).comp htend).sub htend
  exact le_of_tendsto hcont.norm (Filter.Eventually.of_forall (fun k => hmod k h))

/-- A sharper limit form of `transL2_sub_le_of_tendsto`: the per-term moduli `Λ k` need only
converge to `Λ`, not be uniformly bounded by it. This is the form a Sobolev function uses, since
its smooth approximants have gradient norms that converge to, but need not equal, its own. -/
theorem transL2_sub_le_of_tendsto' {g : EucL2 n} {Λ : ℝ} {gk : ℕ → EucL2 n} {Λk : ℕ → ℝ}
    (htend : Filter.Tendsto gk Filter.atTop (nhds g))
    (hΛ : Filter.Tendsto Λk Filter.atTop (nhds Λ))
    (hmod : ∀ k, ∀ h, ‖transL2 h (gk k) - gk k‖ ≤ Λk k * ‖h‖)
    (h : EuclideanSpace ℝ (Fin n)) : ‖transL2 h g - g‖ ≤ Λ * ‖h‖ := by
  have hcont : Filter.Tendsto (fun k => transL2 h (gk k) - gk k) Filter.atTop
      (nhds (transL2 h g - g)) :=
    (((transL2 h).continuous.tendsto g).comp htend).sub htend
  exact le_of_tendsto_of_tendsto' hcont.norm (hΛ.mul_const ‖h‖) (fun k => hmod k h)

end MeasureTheory
