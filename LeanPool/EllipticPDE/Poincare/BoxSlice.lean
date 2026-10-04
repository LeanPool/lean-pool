/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Poincare.Geometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace


/-!
# Discharging the box Poincaré slice bound from the Euclidean geometry

`Poincare/Geometry.lean` reduces coercivity of the bilinear form of the Laplacian on a domain `Ω`
to the
**slice bound**

  `∫_Ω φ² ≤ C · ∫_Ω (∂ᵢφ)²`   (`hslice`, every test function, every direction `i`),

phrased on `EuclideanSpace ℝ (Fin (n+1))`. The one-dimensional/Fubini machinery of
`Poincare/Fubini.lean` proves exactly this bound, but on the **plain product** `Fin (n+1) → ℝ`
with the pi-Lebesgue measure (`poincare_box_dir`). This file is the missing transport: it moves
`poincare_box_dir` across the measure-preserving identification `WithLp.toLp` between
`Fin (n+1) → ℝ` and `EuclideanSpace ℝ (Fin (n+1))`, turning it into the slice bound on a
coordinate box, and hence into **unconditional** coercivity of the bilinear form of the Laplacian
on that box.

The three bridges:

* `toLp_insertNth_eq`: a coordinate slice of the box, reconstructed through `toLp`, is the affine
  line `c + s • eᵢ` in `EuclideanSpace`. This identifies the 1-D slice derivative used by
  `poincare_box_dir` with the Fréchet partial `partialD i φ` (`hasDerivAt_slice`).
* the measure-preserving equivalence `MeasurableEquiv.toLp` (`EuclideanSpace.volume_preserving …`)
  transports the box integrals and the integrability hypotheses between the two spaces.
* the left-face values vanish because `tsupport φ` sits inside the *open* box.

The headline results are `slice_bound_euclBox` (the per-direction Poincaré bound on the box) and
`laplaceBilin_coercive_euclBox` (Dirichlet coercivity on any open box, no abstract hypothesis).
-/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- The open coordinate box `∏ₖ (aₖ, bₖ)` inside `EuclideanSpace ℝ (Fin (n+1))`. -/
def euclBox (a b : Fin (n + 1) → ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | ∀ k, x k ∈ Set.Ioo (a k) (b k)}

/-- The open coordinate box is open: it is a finite intersection of coordinate
preimages of open intervals. -/
lemma isOpen_euclBox (a b : Fin (n + 1) → ℝ) : IsOpen (euclBox a b) := by
  have h : euclBox a b
      = ⋂ k, (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x k) ⁻¹' Set.Ioo (a k) (b k) := by
    ext x
    simp [euclBox, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_Ioo.preimage ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous)

/-- A coordinate slice `s ↦ i.insertNth s y`, transported into `EuclideanSpace` by `toLp`, is the
affine line `toLp (i.insertNth 0 y) + s • eᵢ`. -/
lemma toLp_insertNth_eq (i : Fin (n + 1)) (y : Fin n → ℝ) (s : ℝ) :
    (WithLp.toLp 2 (i.insertNth s y) : EuclideanSpace ℝ (Fin (n + 1)))
      = WithLp.toLp 2 (i.insertNth (0 : ℝ) y) + s • EuclideanSpace.single i (1 : ℝ) := by
  apply PiLp.ext
  intro k
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]; simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove,
      ite_eq_right (Fin.succAbove_ne i j)]; ring

/-- The slice of a test function along coordinate `i`, reconstructed through `toLp`, is
differentiable with derivative the `i`-th classical partial `partialD i φ`. -/
lemma hasDerivAt_slice {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : Differentiable ℝ φ)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => φ (WithLp.toLp 2 (i.insertNth s y)))
      (partialD i φ (WithLp.toLp 2 (i.insertNth t y))) t := by
  set v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single i (1 : ℝ) with hv
  set c : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (i.insertNth (0 : ℝ) y) with hc
  have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hl : HasDerivAt (fun s : ℝ => c + s • v) v t := h1.const_add c
  have hcomp := ((hφ (c + t • v)).hasFDerivAt).comp_hasDerivAt t hl
  simp only [toLp_insertNth_eq, ← hc, ← hv]
  rw [partialD, ← hv]
  exact hcomp

/-- **Per-direction Poincaré bound on an open box** (the slice bound `hslice`). For a test
function `φ` supported in the open box `∏ₖ (aₖ, bₖ)` of `EuclideanSpace ℝ (Fin (n+1))`,
`∫ φ² ≤ (bᵢ - aᵢ)² / 2 · ∫ (∂ᵢφ)²`. This is `poincare_box_dir` (the 1-D/Fubini bound on the plain
product) transported across the measure-preserving `toLp`. -/
theorem slice_bound_euclBox (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn (euclBox a b) φ) (i : Fin (n + 1)) :
    ∫ x in euclBox a b, (φ x) ^ 2
      ≤ (b i - a i) ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 := by
  classical
  have hφd : Differentiable ℝ φ := h.1.differentiable (by simp)
  set P : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun k => Set.Ioo (a k) (b k) with hP
  set e : (Fin (n + 1) → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (n + 1)) :=
    MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ) with he
  have hmp : MeasurePreserving (⇑e) (volume) (volume) := PiLp.volume_preserving_toLp (Fin (n + 1))
  have hme : MeasurableEmbedding (⇑e) := e.measurableEmbedding
  -- The image of the pi-box under `toLp` is the Euclidean box.
  have hbox : (⇑e) '' P = euclBox a b := by
    rw [e.image_eq_preimage_symm]
    ext x
    simp only [hP, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, euclBox, Set.mem_ofPred_eq]
    rfl
  -- Transport any box integral from `EuclideanSpace` to the pi-box.
  have htr : ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ∫ z in euclBox a b, g z = ∫ x in P, g (WithLp.toLp 2 x) := by
    intro g
    rw [← hbox]
    exact hmp.setIntegral_image_emb hme g P
  -- Whole-space integrability of the relevant squares (continuous, compact support).
  have hφ2 : Integrable (fun z => (φ z) ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) :=
    (h.continuous.fun_pow 2).integrable_of_hasCompactSupport
      (by simpa only [Function.comp_def] using
        h.2.1.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num))
  have hpd2 : Integrable (fun z => (partialD i φ z) ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) :=
    ((h.continuous_partialD i).fun_pow 2).integrable_of_hasCompactSupport
      (by simpa only [Function.comp_def] using
        (h.hasCompactSupport_partialD i).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num))
  -- Integrability of the pulled-back squares on the pi-box.
  have hu2 : IntegrableOn (fun x => (φ (WithLp.toLp 2 x)) ^ 2) P volume := by
    have hi := (hmp.integrableOn_image hme (f := fun z => (φ z) ^ 2) (s := P)).mp
    rw [hbox] at hi
    exact hi hφ2.integrableOn
  have hu'2 : IntegrableOn (fun x => (partialD i φ (WithLp.toLp 2 x)) ^ 2) P volume := by
    have hi := (hmp.integrableOn_image hme (f := fun z => (partialD i φ z) ^ 2) (s := P)).mp
    rw [hbox] at hi
    exact hi hpd2.integrableOn
  -- Slice continuity and left-face vanishing.
  have hcont : ∀ y : Fin n → ℝ,
      ContinuousOn (fun s => partialD i φ (WithLp.toLp 2 (i.insertNth s y)))
        (uIcc (a i) (b i)) := by
    intro y
    apply Continuous.continuousOn
    have heq : (fun s => partialD i φ (WithLp.toLp 2 (i.insertNth s y)))
        = fun s => partialD i φ
            (WithLp.toLp 2 (i.insertNth (0 : ℝ) y) + s • EuclideanSpace.single i (1 : ℝ)) :=
      funext fun s => by rw [toLp_insertNth_eq]
    rw [heq]
    exact (h.continuous_partialD i).comp (by fun_prop)
  have hzero : ∀ y : Fin n → ℝ, φ (WithLp.toLp 2 (i.insertNth (a i) y)) = 0 := by
    intro y
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hkey := (h.2.2 hmem i).1
    rw [PiLp.toLp_apply, Fin.insertNth_apply_same] at hkey
    exact lt_irrefl (a i) hkey
  -- Transport both integrals, then apply the 1-D/Fubini box bound.
  rw [htr (fun z => (φ z) ^ 2), htr (fun z => (partialD i φ z) ^ 2)]
  exact poincare_box_dir (u := fun x => φ (WithLp.toLp 2 x))
    (u' := fun x => partialD i φ (WithLp.toLp 2 x)) i (hab i)
    (fun y t _ => hasDerivAt_slice hφd i y t) hcont hzero hu2 hu'2

/-- **Unconditional Dirichlet coercivity on an open box** (the closing Examples remark
of Evans §6.2.2, geometry supplied). With
`C` an upper bound for every side contribution `(bᵢ - aᵢ)² / 2`, the Poisson (Dirichlet) form is
coercive on `H₀¹` of the open box `∏ₖ (aₖ, bₖ)`, with no abstract Poincaré hypothesis: the slice
bound is discharged from the box geometry by `slice_bound_euclBox`. -/
theorem laplaceBilin_coercive_euclBox (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k)
    (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C) :
    IsCoercive (EllipticPdes.laplaceBilin (euclBox a b)) := by
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  refine laplaceBilin_coercive_of_slices (Ω := euclBox a b) (Nat.succ_pos n) C hCnonneg ?_
  intro φ hφ i
  calc ∫ x in euclBox a b, (φ x) ^ 2
      ≤ (b i - a i) ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 :=
        slice_bound_euclBox a b hab hφ i
    _ ≤ C * ∫ x in euclBox a b, (partialD i φ x) ^ 2 :=
        mul_le_mul_of_nonneg_right (hC i) (integral_nonneg (fun x => sq_nonneg _))

/-- **Poincaré inequality on a box** (Theorem `thm: poincare`). For every
`U ∈ H₀¹(Ω)` of the open coordinate box `Ω = ∏ₖ (aₖ, bₖ)` whose side lengths are bounded
by `L`,

  `‖u‖²_{L²(Ω)} ≤ L² / (2 (n + 1)) · ‖∇u‖²_{L²(Ω)}`,

i.e. `‖u‖_{L²} ≤ C_P ‖∇u‖_{L²}` with `C_P = L / √(2 (n + 1))`; taking `L` the maximal
side length gives the diameter-based constant. In the graph encoding the function part is
`U 0` and the gradient components are `U i.succ`. The chain is fully discharged from the
box geometry: the one-dimensional/Fubini slice bound (`slice_bound_euclBox`, resting on
`poincare_box_dir`) is averaged over the `n + 1` directions (`poincare_testfn`) and
extended from the test functions to `H₀¹` by density (`poincare_H01`); no abstract
Poincaré hypothesis remains. -/
theorem poincare_H01_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {L : ℝ} (hL : ∀ i, b i - a i ≤ L)
    {U : H1amb (euclBox a b)} (hU : U ∈ H01 (euclBox a b)) :
    ‖U 0‖ ^ 2 ≤ L ^ 2 / (2 * (n + 1)) * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  have hL0 : 0 ≤ L := le_trans (sub_nonneg.mpr (hab 0)) (hL 0)
  -- The per-direction slice bound, with every side contribution bounded by `L² / 2`.
  have hslice : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      (h : IsTestFn (euclBox a b) φ) (i : Fin (n + 1)),
      ∫ x in euclBox a b, (φ x) ^ 2
        ≤ L ^ 2 / 2 * ∫ x in euclBox a b, (partialD i φ x) ^ 2 := by
    intro φ h i
    refine le_trans (slice_bound_euclBox a b hab h i)
      (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun x => sq_nonneg _))
    have hside : (b i - a i) ^ 2 ≤ L ^ 2 := by
      have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
      nlinarith [hL i]
    linarith
  -- Average over the directions, then extend to `H₀¹` by density.
  have h := poincare_H01 (Ω := euclBox a b) _
    (fun {_φ} hφ => poincare_testfn (Nat.succ_pos n) (L ^ 2 / 2)
      (fun {_ψ} h' i => hslice h' i) hφ) hU
  refine le_trans h (le_of_eq ?_)
  rw [div_div]
  norm_cast

/-- The test-function instance of the box Poincaré inequality, in the slice-constant form
the coercivity layer consumes: with every side contribution `(bᵢ - aᵢ)² / 2` bounded by
`C`, every test function on the box obeys the graph-coordinate bound with constant
`C / (n + 1)`. Derived from the box Poincaré inequality `poincare_H01_euclBox` applied to
the test-function graph (which lies in `H₀¹`), with `L = √(2C)` bounding the sides. -/
theorem testfn_bound_euclBox {a b : Fin (n + 1) → ℝ} (hab : ∀ k, a k ≤ b k)
    {C : ℝ} (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn (euclBox a b) φ) :
    ‖(h.testGraph 0 : L2D (euclBox a b))‖ ^ 2
      ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have h2C : (0 : ℝ) ≤ 2 * C := by linarith
  have hL : ∀ i, b i - a i ≤ Real.sqrt (2 * C) := by
    intro i
    have h1 : 0 ≤ b i - a i := sub_nonneg.mpr (hab i)
    have h2 : (b i - a i) ^ 2 ≤ 2 * C := by linarith [hC i]
    calc b i - a i = Real.sqrt ((b i - a i) ^ 2) := (Real.sqrt_sq h1).symm
      _ ≤ Real.sqrt (2 * C) := Real.sqrt_le_sqrt h2
  have hmem : h.testGraph ∈ H01 (euclBox a b) :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ, h, rfl⟩)
  have hp := poincare_H01_euclBox hab hL hmem
  rw [Real.sq_sqrt h2C] at hp
  refine le_trans hp (le_of_eq ?_)
  rw [mul_div_mul_left C ((n : ℝ) + 1) two_ne_zero]

end EllipticPdes.Poincare
