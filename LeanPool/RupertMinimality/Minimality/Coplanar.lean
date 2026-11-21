/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.FirstOrder
public import LeanPool.RupertMinimality.Minimality.DoubleNormal

/-! # Coplanar -/

@[expose] public section

namespace RupertMinimality

/-!
# L2, L4, L5: the coplanar-silhouette theorem

* L2 (`screenVel_of_depth_eq`, `exists_motion_of_admissible`): on a
  non-vertical plane `z = ⟪g, p⟫ + c` the screen velocity is the affine field
  `M p + b` with `M = ψ J + f gᵀ`; for `g ≠ 0` every `M` with
  `⟪J g, M (J g)⟫ = 0` is realized (`J g` spans the iso-depth direction `û`).
  (The converse, and the face-on case `g = 0`, are not needed and not
  formalized.)
* `admissibleViews V W` (written `U_Π` for `Π = affineSpan W`): the view
  directions `u` not parallel to `Π` such that every other point of `V`
  projects along `u` into the relative interior of `F₀ = conv W`.
* L5 (`exists_firstOrderInward_of_plane`): the coplanar-silhouette theorem in
  the standard view, for an explicit plane.  The headline
  `isRupert_of_admissibleViews_nonempty` is proved in Crossing.lean, via the
  waist lemma (Pyramid.lean); the genericity statement L4 is not needed.

Formulation.  Instead of `W = V ∩ Π` for a plane `Π` we allow any `W ⊆ V`, with
`Π := affineSpan ℝ W`; points of `V \ W` that happen to lie in `Π` must then
lie in `relint F₀`, which the definition of `admissibleViews` already says.
No vertex or convex-position hypothesis is needed, nor nonempty interior of
`conv V`.  Non-collinearity of `W` is needed (a segment shadow has empty
interior); `Π` being a plane follows from `admissibleViews V W ≠ ∅`.
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- The vector `f = (ω₂, -ω₁)` in `M = ψ J + f gᵀ` (L2; indices shifted to `0, 1`). -/
noncomputable def tiltVec (ω : ℝ³) : ℝ² := !₂[ω 1, -ω 0]

/-- **L2, screen velocity on a plane.** On the plane `z = ⟪g, p⟫ + c` the
screen velocity is affine in the screen position `p`:
`ν(x) = ψ J p + ⟪g, p⟫ f + (c f + Pτ)`. -/
theorem screenVel_of_depth_eq (ω τ x : ℝ³) (g : ℝ²) (c : ℝ)
    (hx : x 2 = ⟪g, projXy x⟫ + c) :
    screenVel ω τ x = ω 2 • rot90 (projXy x) + ⟪g, projXy x⟫ • tiltVec ω +
      (c • tiltVec ω + projXy τ) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two] at hx
  ext i
  fin_cases i <;>
    simp [screenVel, projXy, crossMatrix, rot90, tiltVec, Matrix.toLpLin_apply,
      dotProduct, Fin.sum_univ_three, PiLp.inner_apply, Fin.sum_univ_two] at hx ⊢
  · linear_combination (ω 1) * hx
  · linear_combination (-ω 0) * hx

theorem linearMap_apply_coord (M : ℝ² →ₗ[ℝ] ℝ²) (p : ℝ²) (i : Fin 2) :
    M p i = p 0 * M (EuclideanSpace.single 0 1) i + p 1 * M (EuclideanSpace.single 1 1) i := by
  have hp : p = p 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      p 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext j; fin_cases j <;> simp
  conv_lhs => rw [hp]
  simp [map_add, map_smul]

/-- **L2, realization.** For `g ≠ 0`, every affine field `M p + b` with
`⟪J g, M (J g)⟫ = 0` is the screen velocity of some first-order motion on the
plane `z = ⟪g, p⟫ + c` (the direction used by Theorem 5). -/
theorem exists_motion_of_admissible (g : ℝ²) (hg : g ≠ 0) (c : ℝ) (M : ℝ² →ₗ[ℝ] ℝ²)
    (b : ℝ²) (hM : ⟪rot90 g, M (rot90 g)⟫ = 0) :
    ∃ ω τ : ℝ³, ∀ x : ℝ³, x 2 = ⟪g, projXy x⟫ + c →
        screenVel ω τ x = M (projXy x) + b := by
  obtain ⟨A, hA⟩ : ∃ A, M (EuclideanSpace.single 0 1) 0 = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, M (EuclideanSpace.single 1 1) 0 = B := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, M (EuclideanSpace.single 0 1) 1 = C := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, M (EuclideanSpace.single 1 1) 1 = D := ⟨_, rfl⟩
  have hcond : A * g 1 ^ 2 + D * g 0 ^ 2 - (B + C) * (g 0 * g 1) = 0 := by
    have := hM
    rw [PiLp.inner_apply, Fin.sum_univ_two, linearMap_apply_coord M (rot90 g),
      linearMap_apply_coord M (rot90 g), hA, hB, hC, hD] at this
    simp [rot90] at this
    linear_combination this
  have hN : g 0 ^ 2 + g 1 ^ 2 ≠ 0 := by
    intro h0
    apply hg
    have h0' : g 0 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1)]
    have h1' : g 1 = 0 := by nlinarith [sq_nonneg (g 0), sq_nonneg (g 1)]
    ext i; fin_cases i <;> simp [h0', h1']
  obtain ⟨N, hNd⟩ : ∃ N, N = g 0 ^ 2 + g 1 ^ 2 := ⟨_, rfl⟩
  rw [← hNd] at hN
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero 2 hN
  obtain ⟨psiN, hpsi⟩ : ∃ q, q = -(g 0 * (-(A * g 1) + B * g 0) + g 1 * (-(C * g 1) + D * g 0)) :=
    ⟨_, rfl⟩
  obtain ⟨f0N, hf0⟩ : ∃ q, q = (A * g 0 + B * g 1) * N + g 1 * psiN := ⟨_, rfl⟩
  obtain ⟨f1N, hf1⟩ : ∃ q, q = (C * g 0 + D * g 1) * N - g 0 * psiN := ⟨_, rfl⟩
  have kA : A * N ^ 2 = g 0 * f0N := by
    rw [hf0, hpsi, hNd]; linear_combination (g 1 ^ 2) * hcond
  have kB : B * N ^ 2 = -(psiN * N) + g 1 * f0N := by
    rw [hf0, hpsi, hNd]; linear_combination (-(g 0 * g 1)) * hcond
  have kC : C * N ^ 2 = psiN * N + g 0 * f1N := by
    rw [hf1, hpsi, hNd]; linear_combination (-(g 0 * g 1)) * hcond
  have kD : D * N ^ 2 = g 1 * f1N := by
    rw [hf1, hpsi, hNd]; linear_combination (g 0 ^ 2) * hcond
  set f0 := f0N / N ^ 2
  set f1 := f1N / N ^ 2
  set ψ := psiN / N
  have eA : A = g 0 * f0 := by
    rw [mul_div_assoc', eq_div_iff hN2]; exact kA
  have eB : B = -ψ + g 1 * f0 := by
    have : -ψ + g 1 * f0 = (-(psiN * N) + g 1 * f0N) / N ^ 2 := by
      simp only [ψ, f0]; field_simp
    rw [this, eq_div_iff hN2]; exact kB
  have eC : C = ψ + g 0 * f1 := by
    have : ψ + g 0 * f1 = (psiN * N + g 0 * f1N) / N ^ 2 := by
      simp only [ψ, f1]; field_simp
    rw [this, eq_div_iff hN2]; exact kC
  have eD : D = g 1 * f1 := by
    rw [mul_div_assoc', eq_div_iff hN2]; exact kD
  refine ⟨!₂[-f1, f0, ψ], !₂[b 0 - c * f0, b 1 - c * f1, 0], fun x hx => ?_⟩
  rw [screenVel_of_depth_eq _ _ x g c hx]
  have hMp : M (projXy x) = !₂[x 0 * A + x 1 * B, x 0 * C + x 1 * D] := by
    ext i
    rw [linearMap_apply_coord M]
    fin_cases i <;> simp [hA, hB, hC, hD, projXy]
  rw [hMp]
  ext i
  fin_cases i
  · simp [rot90, tiltVec, projXy, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (-x 0) * eA + (-x 1) * eB
  · simp [rot90, tiltVec, projXy, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination (-x 0) * eC + (-x 1) * eD

/-- The admissible views `U_Π` for `Π = affineSpan ℝ W`, `F₀ = conv W`: directions `u`
not parallel to `Π` such that the line `v + ℝ u` meets `relint F₀` for every
`v ∈ V \ W`. -/
def admissibleViews (V W : Finset ℝ³) : Set ℝ³ :=
  { u | u ∉ (affineSpan ℝ (W : Set ℝ³)).direction ∧
    ∀ v ∈ V, v ∉ W → ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³)) }

/-- **Theorem 5, first-order form, standard view, explicit plane** (the form
the proofs use).  `W` lies in the non-vertical plane `⟪N, x⟫ = h`; its
shadow `F = conv (projXy W)` is solid; every other point of `V` projects
into `interior F`; and no double normal of `conv W` is horizontal.  Then some
first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_plane (V W : Finset ℝ³) (hWV : W ⊆ V) (N : ℝ³) (h : ℝ)
    (hN : N 2 ≠ 0) (hWN : ∀ w ∈ W, ⟪N, w⟫ = h)
    (hint : (interior (convexHull ℝ ((W.image projXy : Finset ℝ²) : Set ℝ²))).Nonempty)
    (hin : ∀ v ∈ V, v ∉ W →
      projXy v ∈ interior (convexHull ℝ ((W.image projXy : Finset ℝ²) : Set ℝ²)))
    (hgen : ∀ δ : ℝ³, IsDoubleNormalDir (convexHull ℝ (W : Set ℝ³)) δ → δ 2 ≠ 0) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  classical
  set F₂ := convexHull ℝ ((W.image projXy : Finset ℝ²) : Set ℝ²) with hF₂
  have himgW : projXy '' convexHull ℝ (W : Set ℝ³) = F₂ := by
    rw [hF₂, Finset.coe_image, show (projXy : ℝ³ → ℝ²) = projL from rfl,
      LinearMap.image_convexHull]
  -- the shadow of `conv V` is `F₂`
  have hshadow : projXy '' convexHull ℝ (V : Set ℝ³) = F₂ := by
    rw [show (projXy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
    apply le_antisymm
    · refine convexHull_min ?_ (convex_convexHull ℝ _)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hvW : v ∈ W
      · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hvW))
      · exact interior_subset (hin v hv hvW)
    · rw [hF₂, Finset.coe_image]
      exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hWV))
  -- the plane as a graph `z = ⟪g, p⟫ + c`
  set g : ℝ² := !₂[-(N 0 / N 2), -(N 1 / N 2)] with hg
  set c : ℝ := h / N 2
  have hplane : ∀ x : ℝ³, ⟪N, x⟫ = h → x 2 = ⟪g, projXy x⟫ + c := by
    intro x hx
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial] at hx
    simp only [hg, c, projXy, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      conj_trivial]
    simp
    field_simp
    linear_combination hx
  have hconvW : ∀ x ∈ convexHull ℝ (W : Set ℝ³), ⟪N, x⟫ = h := by
    have : convexHull ℝ (W : Set ℝ³) ⊆ {x | ⟪N, x⟫ = h} :=
      convexHull_min (fun w hw => hWN w hw) (convex_hyperplane (innerₛₗ ℝ N).isLinear h)
    exact fun x hx => this hx
  by_cases hg0 : g = 0
  · -- face-on: impossible, a diameter of `conv W` is a horizontal double normal
    exfalso
    have hN0 : N 0 = 0 := by
      have := congrArg (fun v : ℝ² => v 0) hg0
      simpa [hg, hN] using this
    have hN1 : N 1 = 0 := by
      have := congrArg (fun v : ℝ² => v 1) hg0
      simpa [hg, hN] using this
    obtain ⟨p, hp⟩ := hint
    have hnt : (convexHull ℝ (W : Set ℝ³)).Nontrivial := by
      by_contra hcon
      rw [Set.not_nontrivial_iff] at hcon
      have hsub : F₂.Subsingleton := by
        rw [← himgW]; exact hcon.image _
      have : (interior F₂).Nonempty := ⟨p, hp⟩
      obtain ⟨q, hq⟩ := this
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
      have h1 : q + (r / 2) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈ F₂ :=
        interior_subset (hball (by
          simp [dist_eq_norm, norm_smul, abs_of_pos hr]; linarith))
      have := hsub (interior_subset hq) h1
      have h2 := congrArg (fun v : ℝ² => v 0) this
      simp at h2; linarith
    obtain ⟨δ, a, ha, b, hb, hab, ⟨t, ht⟩, _⟩ :=
      exists_isDoubleNormalDir (W.finite_toSet.isCompact_convexHull ℝ) hnt
    have ht0 : t ≠ 0 := by
      rintro rfl; apply hab; rw [zero_smul, sub_eq_zero] at ht; exact ht.symm
    have hNd : ⟪N, δ⟫ = 0 := by
      have : ⟪N, b - a⟫ = 0 := by rw [inner_sub_right, hconvW a ha, hconvW b hb, sub_self]
      rw [ht, real_inner_smul_right] at this
      exact (mul_eq_zero.mp this).resolve_left ht0
    apply hgen δ ⟨a, ha, b, hb, hab, ⟨t, ht⟩, by assumption⟩
    simpa [PiLp.inner_apply, Fin.sum_univ_three, hN0, hN1, hN] using hNd
  -- the iso-depth direction `J g` and the lifted horizontal vector
  set δ : ℝ³ := !₂[-(g 1), g 0, 0] with hδ
  have hPδ : projXy δ = rot90 g := by
    ext i; fin_cases i <;> simp [hδ, projXy, rot90]
  have hNδ : ⟪N, δ⟫ = 0 := by
    simp [hδ, hg, PiLp.inner_apply, Fin.sum_univ_three]
    field_simp
    ring
  have hnd : ¬ IsDoubleNormalDir F₂ (rot90 g) := by
    rw [← himgW, ← hPδ, ← isDoubleNormalDir_proj_iff' N hN h _ hconvW δ hNδ (by simp [hδ])]
    exact fun hd => hgen δ hd (by simp [hδ])
  have hJg : rot90 g ≠ 0 := by
    intro h0; apply hg0
    have h0' := congrArg (fun v : ℝ² => v 0) h0
    have h1' := congrArg (fun v : ℝ² => v 1) h0
    simp [rot90] at h0' h1'
    ext i; fin_cases i <;> simp [h0', h1']
  obtain ⟨M, b, hM, hinw⟩ := exists_admissible_inward_field _ hint (rot90 g) hJg hnd
  obtain ⟨ω, τ, hωτ⟩ := exists_motion_of_admissible g hg0 c M b hM
  refine ⟨ω, τ, fun v hv => ?_⟩
  rw [hshadow]
  by_cases hvW : v ∈ W
  · rw [hωτ v (hplane v (hWN v hvW))]
    exact hinw _ (Finset.mem_image_of_mem _ hvW)
  · exact isInwardAt_of_mem_interior (hin v hv hvW) _

end Minimality

end RupertMinimality
