/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Form.BilinearForm


/-!
# Characterisation of `H⁻¹(Ω)`

Evans §5.9.1, Theorem 1.

`H⁻¹(Ω)` is the topological dual of `H₀¹(Ω)`; in the graph encoding it is the type
`H01 Ω →L[ℝ] ℝ`. The characterisation theorem says every `f ∈ H⁻¹(Ω)` is represented by
an `(n+1)`-tuple `(f₀, f₁, …, fₙ)` of `L²(Ω)` functions through the pairing

  `⟨f, v⟩ = ∫_Ω (f₀ v - ∑ᵢ fᵢ ∂ᵢv)`,

and that `‖f‖_{H⁻¹}` is the infimum of the tuple norms `(∫_Ω ∑ᵢ |fᵢ|²)^{1/2}` over all
such representations, attained at the Riesz representative.

In the graph encoding a tuple of `L²` functions *is* an element `F` of the ambient space `H1amb
Ω = PiLp 2 (fun _ : Fin (d+1) => L2D Ω)`, and its `PiLp` norm *is* the tuple norm `(∑ᵢ
‖Fᵢ‖²_{L²})^{1/2} = (∫_Ω ∑ᵢ |fᵢ|²)^{1/2}`. The sign convention is the gradient flip `F ↦ (F₀,
-F₁, …, -Fₙ)`, a norm-preserving involution `gradFlip`, under which the representation property
becomes `f v = ⟪gradFlip F, v⟫` in `H1amb Ω`. The proof is then the Riesz representation theorem
on the Hilbert space `H₀¹(Ω)`:

* existence with `‖F‖ = ‖f‖`: flip the Riesz representative of `f`;
* minimality: any representing tuple `G` gives `f` as `⟪gradFlip G, ·⟫` restricted to
  `H₀¹`, so `‖f‖ ≤ ‖gradFlip G‖ = ‖G‖` by Cauchy-Schwarz.

The `L² ⊆ H⁻¹` embedding `l2Functional` (Evans §5.9.1, Theorem 1(iii)) is the instance
with the tuple `(f, 0, …, 0)`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Gradient flip -/

/-- The sign convention adopted here: flip the gradient
coordinates, keeping the function coordinate. A norm-preserving involution of the
ambient space. -/
def gradFlip {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω) : H1amb Ω :=
  WithLp.toLp 2 (Fin.cons (F 0) (fun i => -(F i.succ)))

/-- Simp lemma: the gradient flip fixes the function coordinate, `(gradFlip F) 0 = F 0`. -/
@[simp] lemma gradFlip_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω) :
    gradFlip F 0 = F 0 := by
  rw [gradFlip, PiLp.toLp_apply, Fin.cons_zero]

/-- Simp lemma: `(gradFlip F) i.succ = -(F i.succ)`. -/
@[simp] lemma gradFlip_succ {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω)
    (i : Fin d) : gradFlip F i.succ = -(F i.succ) := by
  rw [gradFlip, PiLp.toLp_apply, Fin.cons_succ]

/-- The gradient flip is an involution. -/
lemma gradFlip_gradFlip {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω) :
    gradFlip (gradFlip F) = F := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [gradFlip_zero, gradFlip_zero]
  · rw [gradFlip_succ, gradFlip_succ, neg_neg]

/-- The gradient flip preserves the ambient (tuple) norm. -/
lemma norm_gradFlip {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω) :
    ‖gradFlip F‖ = ‖F‖ := by
  have h2 : ‖gradFlip F‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [gradFlip_zero]
    · rw [gradFlip_succ, norm_neg]
  calc ‖gradFlip F‖ = Real.sqrt (‖gradFlip F‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖F‖ ^ 2) := by rw [h2]
    _ = ‖F‖ := Real.sqrt_sq (norm_nonneg _)

/-- Pairing a flipped tuple against an ambient vector is exactly the signed sum of
our sign convention: function term minus gradient terms. -/
lemma inner_gradFlip_left {Ω : Set (EuclideanSpace ℝ (Fin d))} (F V : H1amb Ω) :
    ⟪gradFlip F, V⟫ = ⟪F 0, V 0⟫ - ∑ i : Fin d, ⟪F i.succ, V i.succ⟫ := by
  rw [PiLp.inner_apply, Fin.sum_univ_succ, gradFlip_zero]
  have h : ∀ i : Fin d, ⟪gradFlip F i.succ, V i.succ⟫ = -⟪F i.succ, V i.succ⟫ := by
    intro i
    rw [gradFlip_succ, inner_neg_left]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-! ### Representations of functionals by `L²` tuples -/

/-- The tuple `F = (f₀, f₁, …, fₙ)` of `L²(Ω)` functions **represents** the functional
`f ∈ H⁻¹(Ω)` when `⟨f, v⟩ = ⟪f₀, v₀⟫ - ∑ᵢ ⟪fᵢ, ∂ᵢv⟫` for every `v ∈ H₀¹(Ω)`, the
inner-product form of the minus-sign convention adopted here. -/
def IsHnegRepr (Ω : Set (EuclideanSpace ℝ (Fin d))) (F : H1amb Ω)
    (f : H01 Ω →L[ℝ] ℝ) : Prop :=
  ∀ v : H01 Ω,
    f v = ⟪F 0, (v : H1amb Ω) 0⟫ - ∑ i : Fin d, ⟪F i.succ, (v : H1amb Ω) i.succ⟫

/-- A tuple represents `f` exactly when its gradient flip is an ambient Riesz vector
for `f` on `H₀¹`. -/
lemma isHnegRepr_iff_inner {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω)
    (f : H01 Ω →L[ℝ] ℝ) :
    IsHnegRepr Ω F f ↔ ∀ v : H01 Ω, f v = ⟪gradFlip F, (v : H1amb Ω)⟫ := by
  unfold IsHnegRepr
  refine forall_congr' (fun v => ?_)
  rw [inner_gradFlip_left]

/-- The `L²` inner product on `Ω` as an integral, for restating representations in
integral form. -/
lemma inner_L2_eq_integral {Ω : Set (EuclideanSpace ℝ (Fin d))} (a b : L2D Ω) :
    ⟪a, b⟫ = ∫ x in Ω, (a x : ℝ) * (b x : ℝ) := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => Real.inner_apply _ _))

/-- The representation property in integral form:
`⟨f, v⟩ = ∫_Ω f₀ v - ∑ᵢ ∫_Ω fᵢ ∂ᵢv`. -/
lemma isHnegRepr_iff_integral {Ω : Set (EuclideanSpace ℝ (Fin d))} (F : H1amb Ω)
    (f : H01 Ω →L[ℝ] ℝ) :
    IsHnegRepr Ω F f ↔ ∀ v : H01 Ω,
      f v = (∫ x in Ω, (F 0 x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
        - ∑ i : Fin d, ∫ x in Ω, (F i.succ x : ℝ) * ((v : H1amb Ω) i.succ x : ℝ) := by
  simp only [IsHnegRepr, inner_L2_eq_integral]

/-- **Existence of a norm-attaining representation.** The gradient flip of the Riesz
representative of `f` on the Hilbert space `H₀¹(Ω)` represents `f` with tuple norm
exactly `‖f‖_{H⁻¹}`. -/
theorem exists_isHnegRepr_norm_eq (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃ F : H1amb Ω, IsHnegRepr Ω F f ∧ ‖F‖ = ‖f‖ := by
  set w : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hw
  refine ⟨gradFlip (w : H1amb Ω), ?_, ?_⟩
  · rw [isHnegRepr_iff_inner]
    intro v
    rw [gradFlip_gradFlip]
    have h1 : ⟪w, v⟫ = f v := InnerProductSpace.toDual_symm_apply
    have h2 : ⟪(w : H1amb Ω), (v : H1amb Ω)⟫ = ⟪w, v⟫ := rfl
    rw [h2, h1]
  · rw [norm_gradFlip, show ‖(w : H1amb Ω)‖ = ‖w‖ from rfl]
    exact (InnerProductSpace.toDual ℝ (H01 Ω)).symm.norm_map f

/-- **Minimality.** Every representing tuple dominates the dual norm:
`‖f‖_{H⁻¹} ≤ (∫_Ω ∑ᵢ |fᵢ|²)^{1/2}`, by Cauchy-Schwarz against the flipped tuple. -/
theorem norm_le_of_isHnegRepr {Ω : Set (EuclideanSpace ℝ (Fin d))} {F : H1amb Ω}
    {f : H01 Ω →L[ℝ] ℝ} (hF : IsHnegRepr Ω F f) : ‖f‖ ≤ ‖F‖ := by
  rw [isHnegRepr_iff_inner] at hF
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F) (fun v => ?_)
  rw [hF v]
  calc ‖⟪gradFlip F, (v : H1amb Ω)⟫‖
      ≤ ‖gradFlip F‖ * ‖(v : H1amb Ω)‖ := norm_inner_le_norm _ _
    _ = ‖F‖ * ‖v‖ := by rw [norm_gradFlip]; rfl

/-- **Dual norm as the least tuple norm.** The set of norms of representing tuples
has `‖f‖_{H⁻¹}` as a member (the Riesz representative) and as a lower bound (minimality):
the infimum is attained. -/
theorem hneg_norm_isLeast (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : H01 Ω →L[ℝ] ℝ) :
    IsLeast {r : ℝ | ∃ F : H1amb Ω, IsHnegRepr Ω F f ∧ ‖F‖ = r} ‖f‖ := by
  constructor
  · obtain ⟨F, hF, hn⟩ := exists_isHnegRepr_norm_eq Ω f
    exact ⟨F, hF, hn⟩
  · rintro r ⟨F, hF, rfl⟩
    exact norm_le_of_isHnegRepr hF

/-- `‖f‖_{H⁻¹}` as the infimum of the tuple norms over all
representations of `f`.

Terminal result of the library, the infimum form of `hneg_norm_isLeast`.
Nothing else consumes it. -/
theorem hneg_norm_eq_sInf (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : H01 Ω →L[ℝ] ℝ) :
    ‖f‖ = sInf {r : ℝ | ∃ F : H1amb Ω, IsHnegRepr Ω F f ∧ ‖F‖ = r} :=
  ((hneg_norm_isLeast Ω f).csInf_eq).symm

/-- **Characterisation of `H⁻¹(Ω)`** (Evans §5.9.1, Theorem 1, in the sign convention
adopted here). Every continuous linear
functional `f` on `H₀¹(Ω)` is represented by a tuple `F = (f₀, f₁, …, fₙ)` of `L²(Ω)`
functions through `⟨f, v⟩ = ∫_Ω f₀ v - ∑ᵢ ∫_Ω fᵢ ∂ᵢv`, whose
tuple norm `(∫_Ω ∑ᵢ |fᵢ|²)^{1/2} = ‖F‖` equals `‖f‖_{H⁻¹}` and is least among all
representing tuples: the infimum is attained at the Riesz
representative.

Terminal result of the library, stated in the manuscript. Nothing else consumes it. -/
theorem hneg_characterization (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃ F : H1amb Ω,
      (∀ v : H01 Ω,
        f v = (∫ x in Ω, (F 0 x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
          - ∑ i : Fin d, ∫ x in Ω, (F i.succ x : ℝ) * ((v : H1amb Ω) i.succ x : ℝ))
      ∧ ‖F‖ = ‖f‖
      ∧ ∀ G : H1amb Ω,
          (∀ v : H01 Ω,
            f v = (∫ x in Ω, (G 0 x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
              - ∑ i : Fin d, ∫ x in Ω, (G i.succ x : ℝ) * ((v : H1amb Ω) i.succ x : ℝ)) →
          ‖F‖ ≤ ‖G‖ := by
  obtain ⟨F, hF, hn⟩ := exists_isHnegRepr_norm_eq Ω f
  refine ⟨F, (isHnegRepr_iff_integral F f).mp hF, hn, fun G hG => ?_⟩
  rw [hn]
  exact norm_le_of_isHnegRepr ((isHnegRepr_iff_integral G f).mpr hG)

/-! ### `L² ⊆ H⁻¹` embedding -/

/-- The `L² ⊆ H⁻¹` embedding (Evans §5.9.1, Theorem 1(iii)) is the representation by
the tuple
`(f, 0, …, 0)`: a single `L²` function with no gradient terms. -/
lemma isHnegRepr_single_l2Functional (Ω : Set (EuclideanSpace ℝ (Fin d))) (f : L2D Ω) :
    IsHnegRepr Ω (PiLp.single 2 (0 : Fin (d + 1)) f) (l2Functional Ω f) := by
  intro v
  rw [l2Functional_apply, PiLp.single_eq_same]
  rw [Finset.sum_eq_zero, sub_zero]
  intro i _
  rw [PiLp.single_eq_of_ne (p := 2) (Fin.succ_ne_zero i), inner_zero_left]

end EllipticPdes
