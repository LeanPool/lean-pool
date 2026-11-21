/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! # First Order -/

@[expose] public section

namespace RupertMinimality

/-!
# L1: a strictly inward first-order motion gives a passage

Lemma 1 (step 1 of `minimality.md`), in the standard view.  `K = convexHull ℝ V`,
`S = projXy '' K` is the shadow.  A first-order motion `(ω, τ)` is
*strictly inward* (`FirstOrderInward`) if its screen velocity at every point
`v ∈ V` points strictly into `S` at `projXy v`.  For points projecting into
`interior S` this is automatic (`isInwardAt_of_mem_interior`), so the
condition only concerns the points projecting to the boundary of `S`
(`firstOrderInward_iff_frontier`); `V` need not consist of vertices only.

The rotation curve `R_s` is arbitrary as long as `R 0 = 1` and `R' 0 = [ω]×`
entrywise (`eventually_innerShadow_subset`), e.g. `R_s = exp(s[ω]×)`; for the
`IsRupert` corollary we use the Cayley curve
`rotCurve ω s`, the rational rotation with Cayley vector `(s/2)ω`, which is in
`SO(3)` for every `s` (same formula as `Noperts.cayleyMatrix`).
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- The first-order motion `(ω, τ)` moves every point of `V` strictly into
the standard-view shadow `projXy '' conv V`. -/
def FirstOrderInward (V : Finset ℝ³) (ω τ : ℝ³) : Prop :=
  ∀ v ∈ V, IsInwardAt (projXy '' convexHull ℝ (V : Set ℝ³)) (projXy v) (screenVel ω τ v)

/-- Only the boundary points `V_∂ = {v ∈ V : Pv ∈ ∂S}` matter. -/
theorem firstOrderInward_iff_frontier (V : Finset ℝ³) (ω τ : ℝ³) :
    FirstOrderInward V ω τ ↔
      ∀ v ∈ V, projXy v ∈ frontier (projXy '' convexHull ℝ (V : Set ℝ³)) →
        IsInwardAt (projXy '' convexHull ℝ (V : Set ℝ³)) (projXy v) (screenVel ω τ v) := by
  refine ⟨fun h v hv _ => h v hv, fun h v hv => ?_⟩
  by_cases hf : projXy v ∈ frontier (projXy '' convexHull ℝ (V : Set ℝ³))
  · exact h v hv hf
  · apply isInwardAt_of_mem_interior
    have hmem : projXy v ∈ closure (projXy '' convexHull ℝ (V : Set ℝ³)) :=
      subset_closure ⟨v, subset_convexHull ℝ _ hv, rfl⟩
    rw [frontier, Set.mem_sdiff] at hf
    by_contra hni
    exact hf ⟨hmem, hni⟩

/-- **Lemma 1 (analytic core).** Points of a convex set moving with a
one-sided first derivative that is strictly inward at time `0` are eventually
in the interior, uniformly over a finite family. -/
theorem eventually_forall_mem_interior {ι : Type*} (s : Finset ι) {S : Set ℝ²}
    (hS : Convex ℝ S) (φ : ι → ℝ → ℝ²) (d : ι → ℝ²)
    (h0 : ∀ i ∈ s, φ i 0 ∈ closure S)
    (hderiv : ∀ i ∈ s, HasDerivWithinAt (φ i) (d i) (Set.Ici 0) 0)
    (hin : ∀ i ∈ s, IsInwardAt S (φ i 0) (d i)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ s, φ i t ∈ interior S := by
  rw [eventually_all_finset]
  intro i hi
  obtain ⟨ε, hε, hεin⟩ := hin i hi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hεin
  have hlo := (hasDerivWithinAt_iff_isLittleO.mp (hderiv i hi)).def
    (show 0 < r / (2 * ε) by positivity)
  have hlo' := nhdsWithin_mono (0 : ℝ) Set.Ioi_subset_Ici_self hlo
  filter_upwards [hlo', Ioo_mem_nhdsGT hε] with t ht htε
  obtain ⟨ht0, htε⟩ := htε
  simp only [sub_zero, Real.norm_eq_abs, abs_of_pos ht0] at ht
  set e := φ i t - φ i 0 - t • d i with he
  set y := φ i 0 + ε • d i + (ε / t) • e with hy
  have hyin : y ∈ interior S := hball (by
    rw [Metric.mem_ball, dist_eq_norm, hy, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc ε / t * ‖e‖ ≤ ε / t * (r / (2 * ε) * t) := by gcongr
      _ = r / 2 := by field_simp
      _ < r := by linarith)
  have hcomb : (1 - t / ε) • φ i 0 + (t / ε) • y = φ i t := by
    have h1 : t / ε * (ε / t) = 1 := by field_simp
    rw [hy, he, smul_add, smul_add, smul_smul, smul_smul, h1, div_mul_cancel₀ _ hε.ne', one_smul]
    module
  rw [← hcomb]
  exact hS.combo_closure_interior_mem_interior (h0 i hi) hyin
    (by rw [sub_nonneg, div_le_one hε]; exact htε.le) (div_pos ht0 hε) (by ring)


/-- The screen trajectory of a point under a matrix curve has the screen
velocity as derivative. -/
theorem hasDerivAt_proj_curve (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : ∀ i j, HasDerivAt (fun s => R s i j) (A i j) 0) (v : ℝ³) :
    HasDerivAt (fun s => projXy ((R s).toEuclideanLin v)) (projXy (A.toEuclideanLin v)) 0 := by
  have hk : ∀ k : Fin 3, HasDerivAt (fun s => R s k 0 * v 0 + R s k 1 * v 1 + R s k 2 * v 2)
      (A k 0 * v 0 + A k 1 * v 1 + A k 2 * v 2) 0 := fun k =>
    (((hR k 0).mul_const _).add ((hR k 1).mul_const _)).add ((hR k 2).mul_const _)
  have h := ((hk 0).smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).add
    ((hk 1).smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  have hfun : (fun s => projXy ((R s).toEuclideanLin v)) =
      (fun s => (R s 0 0 * v 0 + R s 0 1 * v 1 + R s 0 2 * v 2) •
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
        (fun s => (R s 1 0 * v 0 + R s 1 1 * v 1 + R s 1 2 * v 2) •
          EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    funext s
    ext i
    fin_cases i <;> simp [projXy, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  have hval : projXy (A.toEuclideanLin v) =
      (A 0 0 * v 0 + A 0 1 * v 1 + A 0 2 * v 2) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (A 1 0 * v 0 + A 1 1 * v 1 + A 1 2 * v 2) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [projXy, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  rw [hfun, hval]
  exact h

/-- The inner shadow of a hull is the hull of the inner shadow of the points. -/
theorem innerShadow_convexHull (R : Matrix (Fin 3) (Fin 3) ℝ) (o : ℝ²) (V : Set ℝ³) :
    innerShadow R o (convexHull ℝ V) =
      convexHull ℝ ((fun p => o + projXy (R.toEuclideanLin p)) '' V) := by
  let f : ℝ³ →ᵃ[ℝ] ℝ² := (AffineEquiv.constVAdd ℝ ℝ² o).toAffineMap.comp
    (projL ∘ₗ R.toEuclideanLin).toAffineMap
  have hf : ∀ p, f p = o + projXy (R.toEuclideanLin p) := fun p => by
    simp [f, projL_apply, vadd_eq_add]
  have hfe : (f : ℝ³ → ℝ²) = fun p => o + projXy (R.toEuclideanLin p) := funext hf
  rw [← hfe, ← f.image_convexHull, hfe]
  rfl

/-- **Lemma 1.** If `(ω, τ)` is strictly inward, then for every curve of
matrices `R` with `R 0 = 1` and `R' 0 = [ω]×` (entrywise), and all small
`s > 0`, the shadow of `R_s K + sτ` lies in the interior of the shadow of `K`:
`P(R_s K + sτ) ⊆ int P(K)`. -/
theorem eventually_innerShadow_subset (V : Finset ℝ³) (ω τ : ℝ³)
    (h : FirstOrderInward V ω τ) (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hR0 : R 0 = 1)
    (hR : ∀ i j, HasDerivAt (fun s => R s i j) (crossMatrix ω i j) 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      innerShadow (R s) (s • projXy τ) (convexHull ℝ (V : Set ℝ³)) ⊆
        interior (outerShadow 1 (convexHull ℝ (V : Set ℝ³))) := by
  rw [outerShadow_one]
  set S := projXy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hS : Convex ℝ S := by
    rw [hSdef, show (projXy : ℝ³ → ℝ²) = projL from rfl]
    exact (convex_convexHull ℝ _).linear_image projL
  have hev := eventually_forall_mem_interior V hS
    (fun v s => s • projXy τ + projXy ((R s).toEuclideanLin v)) (fun v => screenVel ω τ v)
    (fun v hv => subset_closure ⟨v, subset_convexHull ℝ _ hv, by simp [hR0]⟩)
    (fun v _ => by
      have := ((hasDerivAt_id' (0 : ℝ)).smul_const (projXy τ)).add
        (hasDerivAt_proj_curve R (crossMatrix ω) hR v)
      have hval : screenVel ω τ v = (1 : ℝ) • projXy τ +
        projXy ((crossMatrix ω).toEuclideanLin v) := by
        simp [screenVel, proj_xy_add', add_comm]
      rw [hval]
      exact this.hasDerivWithinAt)
    (fun v hv => by simpa [hR0] using h v hv)
  filter_upwards [hev] with s hs
  rw [innerShadow_convexHull]
  refine convexHull_min ?_ hS.interior
  rintro _ ⟨v, hv, rfl⟩
  exact hs v hv

/-- Denominator of the Cayley rotation. -/
def cayleyDen (v : ℝ³) : ℝ := 1 + v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

theorem cayleyDen_pos (v : ℝ³) : 0 < cayleyDen v := by unfold cayleyDen; positivity

/-- The Cayley rotation with Cayley vector `v` (the unit quaternion
proportional to `(1, v)`); the same matrix as `Noperts.cayleyMatrix`. -/
noncomputable def cayley (v : ℝ³) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 + v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2) / cayleyDen v, 2 * (v 0 * v 1 - v 2) / cayleyDen v,
      2 * (v 0 * v 2 + v 1) / cayleyDen v;
     2 * (v 0 * v 1 + v 2) / cayleyDen v, (1 - v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2) / cayleyDen v,
      2 * (v 1 * v 2 - v 0) / cayleyDen v;
     2 * (v 0 * v 2 - v 1) / cayleyDen v, 2 * (v 1 * v 2 + v 0) / cayleyDen v,
      (1 - v 0 ^ 2 - v 1 ^ 2 + v 2 ^ 2) / cayleyDen v]

/-- A rotation curve through the identity with angular velocity `ω`. -/
noncomputable def rotCurve (ω : ℝ³) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  cayley ((s / 2) • ω)

theorem cayley_mem_SO3 (v : ℝ³) : cayley v ∈ SO3 := by
  have hd := (cayleyDen_pos v).ne'
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cayley, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;>
      simp only [cayleyDen] <;> ring
  · simp [cayley, Matrix.det_fin_three]
    field_simp
    simp only [cayleyDen]
    ring

theorem rotCurve_zero (ω : ℝ³) : rotCurve ω 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotCurve, cayley, cayleyDen]

/-- A rational function `c + (s a + s² b) / (1 + s² q)` has derivative `a`
at `0`. -/
theorem hasDerivAt_rat_aux (a b c q : ℝ) :
    HasDerivAt (fun s : ℝ => c + (s * a + s ^ 2 * b) / (1 + s ^ 2 * q)) a 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s * a + s ^ 2 * b) (1 * a + (2 * (0:ℝ) ^ 1 * 1) * b) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).mul_const a).add (((hasDerivAt_id' (0 : ℝ)).pow 2).mul_const b)
  have h2 : HasDerivAt (fun s : ℝ => 1 + s ^ 2 * q) ((2 * (0:ℝ) ^ 1 * 1) * q) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).pow 2).mul_const q).const_add 1
  have := (h1.div h2 (by simp)).const_add c
  exact this.congr_deriv (by simp)

/-- Entries of the Cayley curve: `δᵢⱼ + (s Aᵢⱼ + s² (A²)ᵢⱼ / 2) / (1 + s² |ω|²/4)`
with `A = [ω]×`. -/
theorem rotCurve_apply (ω : ℝ³) (s : ℝ) (i j : Fin 3) :
    rotCurve ω s i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j +
      (s * crossMatrix ω i j + s ^ 2 * ((crossMatrix ω * crossMatrix ω) i j / 2)) /
        (1 + s ^ 2 * ((ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2) / 4)) := by
  have hd : (1 + s ^ 2 * ((ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2) / 4)) ≠ 0 := by positivity
  fin_cases i <;> fin_cases j <;>
    simp [rotCurve, cayley, cayleyDen, crossMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

theorem hasDerivAt_rotCurve (ω : ℝ³) (i j : Fin 3) :
    HasDerivAt (fun s => rotCurve ω s i j) (crossMatrix ω i j) 0 := by
  have h := hasDerivAt_rat_aux (crossMatrix ω i j) ((crossMatrix ω * crossMatrix ω) i j / 2)
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j) ((ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2) / 4)
  have hfun : (fun s => rotCurve ω s i j) = fun s : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j +
      (s * crossMatrix ω i j + s ^ 2 * ((crossMatrix ω * crossMatrix ω) i j / 2)) /
        (1 + s ^ 2 * ((ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2) / 4)) := funext fun s => rotCurve_apply ω s i j
  rw [hfun]
  exact h

/-- **Lemma 1, Rupert form** (standard view): a strictly inward first-order
motion makes `V` Rupert, with `R₁ = rotCurve ω s`, offset `s • Pτ`, `R₂ = 1`
for small `s > 0`. -/
theorem isRupert_of_firstOrderInward (V : Finset ℝ³) (ω τ : ℝ³)
    (h : FirstOrderInward V ω τ) : IsRupert V := by
  have hev := eventually_innerShadow_subset V ω τ h (rotCurve ω) (rotCurve_zero ω)
    (hasDerivAt_rotCurve ω)
  obtain ⟨s, hs⟩ := hev.exists
  exact (isRupert_iff_shadows V).mpr
    ⟨rotCurve ω s, cayley_mem_SO3 _, s • projXy τ, 1, one_mem _, hs⟩

/-- **Lemma 1, Rupert form** at the view of a rotation `Q`, i.e. view
direction `Qᵀ ez`. -/
theorem isRupert_of_firstOrderInward_image (V : Finset ℝ³) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q ∈ SO3) (ω τ : ℝ³) (h : FirstOrderInward (V.image Q.toEuclideanLin) ω τ) :
    IsRupert V :=
  isRupert_of_isRupert_image_rotation Q hQ V (isRupert_of_firstOrderInward _ ω τ h)

end Minimality

end RupertMinimality
