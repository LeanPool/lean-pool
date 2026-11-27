/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Proof.ScalarProjection.Defs
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.External.KinderlehrerStampacchia.Projection
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Convex.SupportFunction
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.FundamentalDomain
import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.GradientConstraint
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Rademacher

/-!
# §2, Lemma 4: the projection exists and satisfies the variational inequality

TeX lines 411–415: "The set `𝒞` is nonempty, closed and convex in `L² (Q)`. By
[Kinderlehrer–Stampacchia, Chapter I, Lemma 2.1 and Theorem 2.3], the projection `ζ` exists
uniquely and, with `h (x) = η (x) − ζ (x)`, satisfies `∫_Q h (ξ − ζ) dx ≤ 0` for all `ξ ∈ 𝒞`
(`(eq:projection-variational-inequality)`)."

* `lemma4_exists`: the projection exists;
* `lemma4_unique`, `lemma4_existsUnique`: it is unique, as a Lipschitz periodic function;
* `lemma4_variationalInequality`: `(eq:projection-variational-inequality)`.

All follow the paper through Kinderlehrer and Stampacchia, applied in the Hilbert space
`L² (Q) = Lp ℝ 2 (volume.restrict unitSquare)` to the set `𝒞_{L²}` of the classes with a
representative in `𝒞` (`constraintSetL2`). There the inner product is `∫_Q f g` and the squared norm
is `∫_Q f²`, so the projection of `η` on `𝒞_{L²}` is the class of an `L² (Q)`-projection of `η` on
`𝒞` in the sense of `IsL2Projection`, and conversely.

* `𝒞` is convex (`convex_constraintSet`): a convex combination of Lipschitz periodic functions is
  Lipschitz and periodic, and where both are differentiable (almost everywhere, by Rademacher's
  theorem) its gradient is the convex combination of the gradients.
* `𝒞_{L²}` is nonempty (`0 ∈ 𝒞`, as `p ∈ K`) and closed (`isClosed_constraintSetL2`).

The paper asserts the closedness; the argument here: for `ξ` Lipschitz and periodic, the constraint
`p + Dξ ∈ K` a.e. is equivalent to the slope bound `ξ (y) − ξ (x) + p · (y − x) ≤ H_K (y − x)` for
all `x, y`, with `H_K` the support function of `K` (`sub_add_dotProduct_le_supportFun_of_ae_mem`,
by mollification and the mean value theorem; `add_fderiv_mem_of_sub_add_dotProduct_le_supportFun`
for the converse). The slope bound gives a Lipschitz constant that depends only on `K` and `p`. A
sequence of `𝒞_{L²}` converging in `L² (Q)` has a subsequence converging a.e. on `Q`; its
representatives in `𝒞` are equi-Lipschitz and periodic, so they converge everywhere
(`exists_tendsto_of_ae_restrict_unitCube_tendsto`), and the limit satisfies the slope bound, so it
lies in `𝒞` and represents the `L²` limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory CalculusOfVariations

namespace Agazzi

variable {K : Set (Fin 2 → ℝ)} {p : Fin 2 → ℝ}

open Filter Topology
open scoped InnerProductSpace

/-! ### `𝒞` in `L² (Q)` -/

private theorem measurableSet_unitSquare : MeasurableSet unitSquare :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

private theorem isFiniteMeasure_unitSquare : IsFiniteMeasure (volume.restrict unitSquare) :=
  isFiniteMeasure_restrict.2
    (lt_of_le_of_lt (measure_mono (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self))
      (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).measure_lt_top).ne

/-- A Lipschitz function is in `L² (Q)`: it is bounded on `Q`. -/
private theorem memLp_of_lipPer {ξ : (Fin 2 → ℝ) → ℝ} (hξ : LipPer ξ) :
    MemLp ξ 2 (volume.restrict unitSquare) := by
  have := isFiniteMeasure_unitSquare
  obtain ⟨C, hC⟩ := hξ.1
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)
    ).exists_bound_of_continuousOn hC.continuous.continuousOn
  exact MemLp.of_bound hC.continuous.aestronglyMeasurable M
    (ae_restrict_of_forall_mem measurableSet_unitSquare fun x hx =>
      hM x (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self) hx))

/-- The inner product of `L² (Q)` is `∫_Q f g`. -/
private theorem inner_eq_integral {u w : Lp ℝ 2 (volume.restrict unitSquare)}
    {f g : (Fin 2 → ℝ) → ℝ} (hu : u =ᵐ[volume.restrict unitSquare] f)
    (hw : w =ᵐ[volume.restrict unitSquare] g) :
    ⟪u, w⟫_ℝ = ∫ x in unitSquare, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hw] with x hx hx'
  rw [Real.inner_apply, hx, hx']

/-- The squared norm of `L² (Q)` is `∫_Q f²`. -/
private theorem norm_sq_eq_integral {u : Lp ℝ 2 (volume.restrict unitSquare)}
    {f : (Fin 2 → ℝ) → ℝ} (hu : u =ᵐ[volume.restrict unitSquare] f) :
    ‖u‖ ^ 2 = ∫ x in unitSquare, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral hu hu]
  simp_rw [sq]

private theorem coeFn_sub_ae {u w : Lp ℝ 2 (volume.restrict unitSquare)}
    {f g : (Fin 2 → ℝ) → ℝ} (hu : u =ᵐ[volume.restrict unitSquare] f)
    (hw : w =ᵐ[volume.restrict unitSquare] g) :
    (⇑(u - w)) =ᵐ[volume.restrict unitSquare] fun x => f x - g x := by
  filter_upwards [Lp.coeFn_sub u w, hu, hw] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- `𝒞` in `L² (Q)`: the classes with a representative in `𝒞`. -/
private def constraintSetL2 (K : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) :
    Set (Lp ℝ 2 (volume.restrict unitSquare)) :=
  {u | ∃ ξ ∈ constraintSet K p, (u : (Fin 2 → ℝ) → ℝ) =ᵐ[volume.restrict unitSquare] ξ}

private theorem toLp_mem_constraintSetL2 {ξ : (Fin 2 → ℝ) → ℝ} (hξ : ξ ∈ constraintSet K p) :
    (memLp_of_lipPer hξ.1).toLp ξ ∈ constraintSetL2 K p :=
  ⟨ξ, hξ, MemLp.coeFn_toLp _⟩

/-- `𝒞` is convex. -/
private theorem convex_constraintSet (hKcv : Convex ℝ K) : Convex ℝ (constraintSet K p) := by
  intro ξ₁ h₁ ξ₂ h₂ a b ha hb hab
  obtain ⟨⟨⟨C₁, hC₁⟩, hp₁⟩, hK₁⟩ := h₁
  obtain ⟨⟨⟨C₂, hC₂⟩, hp₂⟩, hK₂⟩ := h₂
  refine ⟨⟨⟨‖a‖₊ * C₁ + ‖b‖₊ * C₂, ?_⟩, ?_⟩, ?_⟩
  · exact ((lipschitzWith_smul a).comp hC₁).add ((lipschitzWith_smul b).comp hC₂)
  · intro x k
    simp only [Pi.add_apply, Pi.smul_apply, hp₁ x k, hp₂ x k]
  · filter_upwards [hK₁, hK₂, ae_restrict_of_ae hC₁.ae_differentiableAt,
      ae_restrict_of_ae hC₂.ae_differentiableAt] with x hx₁ hx₂ hd₁ hd₂
    have hfd : fderiv ℝ (a • ξ₁ + b • ξ₂) x = a • fderiv ℝ ξ₁ x + b • fderiv ℝ ξ₂ x :=
      ((hd₁.hasFDerivAt.const_smul a).add (hd₂.hasFDerivAt.const_smul b)).fderiv
    have : p + sgrad (a • ξ₁ + b • ξ₂) x = a • (p + sgrad ξ₁ x) + b • (p + sgrad ξ₂ x) := by
      ext j
      simp only [sgrad, hfd, Pi.add_apply, Pi.smul_apply, add_apply, FunLike.coe_smul,
        smul_eq_mul]
      linear_combination (-(p j)) * hab
    rw [this]
    exact hKcv hx₁ hx₂ ha hb hab

private theorem convex_constraintSetL2 (hKcv : Convex ℝ K) : Convex ℝ (constraintSetL2 K p) := by
  rintro u ⟨ξ₁, h₁, hu⟩ w ⟨ξ₂, h₂, hw⟩ a b ha hb hab
  refine ⟨a • ξ₁ + b • ξ₂, convex_constraintSet hKcv h₁ h₂ ha hb hab, ?_⟩
  filter_upwards [Lp.coeFn_add (a • u) (b • w), Lp.coeFn_smul a u, Lp.coeFn_smul b w, hu, hw]
    with x h1 h2 h3 h4 h5
  simp only [h1, Pi.add_apply, h2, h3, Pi.smul_apply, h4, h5]

private theorem nonempty_constraintSetL2 (hp : p ∈ K) : (constraintSetL2 K p).Nonempty := by
  refine ⟨0, 0, ⟨⟨⟨0, LipschitzWith.const 0⟩, fun x k => rfl⟩, Eventually.of_forall fun x => ?_⟩,
    Lp.coeFn_zero _ _ _⟩
  have : sgrad 0 x = 0 := by
    ext j
    simp [sgrad, fderiv_zero]
  rw [this, add_zero]
  exact hp

/-- `𝒞_{L²}` is closed (see the module docstring). -/
private theorem isClosed_constraintSetL2 (hKne : K.Nonempty) (hKc : IsCompact K)
    (hKcv : Convex ℝ K) : IsClosed (constraintSetL2 K p) := by
  refine IsSeqClosed.isClosed fun u u₀ hu hlim => ?_
  have hu' : ∀ n, ∃ ξ ∈ constraintSet K p,
      (u n : (Fin 2 → ℝ) → ℝ) =ᵐ[volume.restrict unitSquare] ξ := hu
  choose ξ hξ hξu using hu'
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hslope : ∀ n x y, ξ n y - ξ n x + p ⬝ᵥ (y - x) ≤ supportFun K (y - x) := fun n =>
    sub_add_dotProduct_le_supportFun_of_ae_mem hKc (hξ n).1.1.choose_spec (hξ n).1.2 (hξ n).2
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_sub_add_dotProduct_le_supportFun hKc hKne p
  have hae : ∀ᵐ x ∂(volume.restrict unitSquare),
      Tendsto (fun k => ξ (ns k) x) atTop (𝓝 (u₀ x)) := by
    filter_upwards [hns, ae_all_iff.2 hξu] with x hx hx'
    exact hx.congr fun k => hx' (ns k)
  obtain ⟨ξ', hξ'⟩ := exists_tendsto_of_ae_restrict_unitCube_tendsto
    (fun k => hL _ (hslope (ns k))) (fun k => (hξ (ns k)).1.2) hae
  have hslope' : ∀ x y, ξ' y - ξ' x + p ⬝ᵥ (y - x) ≤ supportFun K (y - x) := fun x y =>
    le_of_tendsto' (((hξ' y).sub (hξ' x)).add_const _) fun k => hslope _ x y
  have hper' : IsPeriodic ξ' := fun x z =>
    tendsto_nhds_unique ((hξ' (x + fun i => (z i : ℝ))).congr fun k => (hξ (ns k)).1.2 x z)
      (hξ' x)
  have hlip' := hL _ hslope'
  refine ⟨ξ', ⟨⟨⟨L, hlip'⟩, hper'⟩, ?_⟩, ?_⟩
  · filter_upwards [ae_restrict_of_ae hlip'.ae_differentiableAt] with x hx
    exact add_fderiv_mem_of_sub_add_dotProduct_le_supportFun hKc hKne hKcv hslope' hx
  · filter_upwards [hae] with x hx
    exact tendsto_nhds_unique hx (hξ' x)

/-- For `ζ ∈ 𝒞`, the `L² (Q)` distance from `η` to `ζ` and to the classes of `𝒞_{L²}`, by their
representatives. -/
private theorem norm_sub_sq_eq {η ξ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η)
    {v : Lp ℝ 2 (volume.restrict unitSquare)} (hv : v =ᵐ[volume.restrict unitSquare] ξ) :
    ‖(memLp_of_lipPer hη).toLp η - v‖ ^ 2 = ∫ x in unitSquare, (η x - ξ x) ^ 2 :=
  norm_sq_eq_integral (coeFn_sub_ae (MemLp.coeFn_toLp _) hv)

private theorem bddBelow_norm_sub (x₀ : Lp ℝ 2 (volume.restrict unitSquare)) :
    BddBelow (Set.range fun v : constraintSetL2 K p => ‖x₀ - v‖) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩

/-- The `L² (Q)`-projection of `η` on `𝒞` exists (TeX line 412).

Proof: `𝒞_{L²}` is nonempty, closed and convex in `L² (Q)`; Kinderlehrer–Stampacchia's Lemma 2.1
(`External.KinderlehrerStampacchia.lemma2_1`) gives the nearest point of `𝒞_{L²}` to `η`, and its
representative in `𝒞` is an `L² (Q)`-projection. -/
theorem lemma4_exists (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K) (hp : p ∈ K)
    {η : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) :
    ∃ ζ, IsL2Projection (constraintSet K p) η ζ := by
  obtain ⟨y, ⟨⟨ζ, hζ, hy⟩, hmin⟩, -⟩ := External.KinderlehrerStampacchia.lemma2_1
    (nonempty_constraintSetL2 hp) (isClosed_constraintSetL2 hKne hKc hKcv)
    (convex_constraintSetL2 hKcv) ((memLp_of_lipPer hη).toLp η)
  refine ⟨ζ, hζ, fun ξ hξ => ?_⟩
  have hle : ‖(memLp_of_lipPer hη).toLp η - y‖ ≤
      ‖(memLp_of_lipPer hη).toLp η - (memLp_of_lipPer hξ.1).toLp ξ‖ := by
    rw [hmin]
    exact ciInf_le (bddBelow_norm_sub _) ⟨_, toLp_mem_constraintSetL2 hξ⟩
  rw [← norm_sub_sq_eq hη hy, ← norm_sub_sq_eq hη (MemLp.coeFn_toLp _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- An `L² (Q)`-projection of `η` on `𝒞` is, as a class of `L² (Q)`, the nearest point of `𝒞_{L²}`
to `η`. -/
private theorem norm_sub_toLp_eq_iInf {η ζ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η)
    (hζ : IsL2Projection (constraintSet K p) η ζ) :
    ‖(memLp_of_lipPer hη).toLp η - (memLp_of_lipPer hζ.1.1).toLp ζ‖ =
      ⨅ v : constraintSetL2 K p, ‖(memLp_of_lipPer hη).toLp η - v‖ := by
  have hy₀ := toLp_mem_constraintSetL2 hζ.1
  have : Nonempty (constraintSetL2 K p) := ⟨⟨_, hy₀⟩⟩
  refine le_antisymm (le_ciInf fun v => ?_) (ciInf_le (bddBelow_norm_sub _) ⟨_, hy₀⟩)
  obtain ⟨ξ', hξ', hv⟩ := v.2
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_eq hη (MemLp.coeFn_toLp _),
    norm_sub_sq_eq hη hv]
  exact hζ.2 ξ' hξ'

/-- The `L² (Q)`-projection is unique (TeX line 412: "the projection `ζ` exists uniquely"): two
`L² (Q)`-projections of `η` on `𝒞` are equal, as Lipschitz periodic functions, the representatives
of `W^{1,∞}_per (Q)` in the formalization; in particular they agree almost everywhere on `Q`.

Proof: their classes in `L² (Q)` are nearest points of `𝒞_{L²}` to `η`, which is nonempty, closed
and convex, so they are equal by the uniqueness in Kinderlehrer–Stampacchia's Lemma 2.1
(`External.KinderlehrerStampacchia.lemma2_1`): the two functions agree almost everywhere on `Q`.
Being periodic, they agree almost everywhere on `ℝ²`
(`CalculusOfVariations.ae_of_ae_restrict_unitCube_of_periodic`), and, being continuous,
everywhere. -/
theorem lemma4_unique (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K) (hp : p ∈ K)
    {η ζ₁ ζ₂ : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) (h₁ : IsL2Projection (constraintSet K p) η ζ₁)
    (h₂ : IsL2Projection (constraintSet K p) η ζ₂) : ζ₁ = ζ₂ := by
  obtain ⟨y, -, hy⟩ := External.KinderlehrerStampacchia.lemma2_1
    (nonempty_constraintSetL2 hp) (isClosed_constraintSetL2 hKne hKc hKcv)
    (convex_constraintSetL2 hKcv) ((memLp_of_lipPer hη).toLp η)
  have e₁ := hy _ ⟨toLp_mem_constraintSetL2 h₁.1, norm_sub_toLp_eq_iInf hη h₁⟩
  have e₂ := hy _ ⟨toLp_mem_constraintSetL2 h₂.1, norm_sub_toLp_eq_iInf hη h₂⟩
  have hQ : ζ₁ =ᵐ[volume.restrict unitSquare] ζ₂ := by
    filter_upwards [(memLp_of_lipPer h₁.1.1).coeFn_toLp, (memLp_of_lipPer h₂.1.1).coeFn_toLp]
      with x hx₁ hx₂
    rw [← hx₁, ← hx₂, e₁, e₂]
  have hR : ζ₁ =ᵐ[volume] ζ₂ :=
    ae_of_ae_restrict_unitCube_of_periodic (P := fun x => ζ₁ x = ζ₂ x)
      (fun x k hxk => by rwa [h₁.1.1.2 x k, h₂.1.1.2 x k] at hxk) hQ
  obtain ⟨C₁, hC₁⟩ := h₁.1.1.1
  obtain ⟨C₂, hC₂⟩ := h₂.1.1.1
  exact (hC₁.continuous.ae_eq_iff_eq volume hC₂.continuous).1 hR

/-- The `L² (Q)`-projection exists and is unique (TeX line 412): `lemma4_exists` and
`lemma4_unique`. -/
theorem lemma4_existsUnique (hKne : K.Nonempty) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (hp : p ∈ K) {η : (Fin 2 → ℝ) → ℝ} (hη : LipPer η) :
    ∃! ζ, IsL2Projection (constraintSet K p) η ζ := by
  obtain ⟨ζ, hζ⟩ := lemma4_exists hKne hKc hKcv hp hη
  exact ⟨ζ, hζ, fun ζ' hζ' => lemma4_unique hKne hKc hKcv hp hη hζ' hζ⟩

/-- `(eq:projection-variational-inequality)`: with `h = η − ζ`, `∫_Q h (ξ − ζ) ≤ 0` for every
`ξ ∈ 𝒞` (TeX lines 412–415).

Proof: the class of `ζ` is the nearest point of the convex `𝒞_{L²}` to `η` in `L² (Q)`, and
Kinderlehrer–Stampacchia's Theorem 2.3 (`External.KinderlehrerStampacchia.theorem2_3`) gives
`⟪η − ζ, ξ − ζ⟫_{L² (Q)} ≤ 0`, which is the integral. -/
theorem lemma4_variationalInequality (hKcv : Convex ℝ K) {η ζ : (Fin 2 → ℝ) → ℝ}
    (hη : LipPer η) (hζ : IsL2Projection (constraintSet K p) η ζ) :
    ∀ ξ ∈ constraintSet K p, ∫ x in unitSquare, (η x - ζ x) * (ξ x - ζ x) ≤ 0 := by
  intro ξ hξ
  have hy₀ := toLp_mem_constraintSetL2 hζ.1
  have : Nonempty (constraintSetL2 K p) := ⟨⟨_, hy₀⟩⟩
  have hnorm : ‖(memLp_of_lipPer hη).toLp η - (memLp_of_lipPer hζ.1.1).toLp ζ‖ =
      ⨅ v : constraintSetL2 K p, ‖(memLp_of_lipPer hη).toLp η - v‖ := by
    refine le_antisymm (le_ciInf fun v => ?_) (ciInf_le (bddBelow_norm_sub _) ⟨_, hy₀⟩)
    obtain ⟨ξ', hξ', hv⟩ := v.2
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_eq hη (MemLp.coeFn_toLp _),
      norm_sub_sq_eq hη hv]
    exact hζ.2 ξ' hξ'
  have hvi := (External.KinderlehrerStampacchia.theorem2_3 (convex_constraintSetL2 hKcv) hy₀).1
    hnorm _ (toLp_mem_constraintSetL2 hξ)
  rwa [inner_eq_integral (coeFn_sub_ae (MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _))
    (coeFn_sub_ae (MemLp.coeFn_toLp _) (MemLp.coeFn_toLp _))] at hvi

end Agazzi
