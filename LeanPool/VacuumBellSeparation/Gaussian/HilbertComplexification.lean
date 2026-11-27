/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Hilbert complexification of a real Hilbert space

The underlying normed additive group is the actual `WithLp 2 (E × E)`.
Complex multiplication and the Hermitian inner product are constructed
explicitly. In particular the norm and completeness are inherited from
the real L² product, rather than supplied as assumptions.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- The real L² product, equipped below with its complex Hilbert structure. -/
def HilbertComplexification (E : Type*) := WithLp 2 (E × E)

namespace HilbertComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable instance : NormedAddCommGroup (HilbertComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

/-- Re. -/
def re (z : HilbertComplexification E) : E := (WithLp.ofLp z).1
/-- Im. -/
def im (z : HilbertComplexification E) : E := (WithLp.ofLp z).2
/-- Mk defined as `WithLp.toLp 2 (x, y)`. -/
def mk (x y : E) : HilbertComplexification E := WithLp.toLp 2 (x, y)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[ext]
theorem ext {z w : HilbertComplexification E} (hre : z.re = w.re) (him : z.im = w.im) :
    z = w := WithLp.ofLp_injective 2 (Prod.ext hre him)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem re_mk (x y : E) : (mk x y).re = x := rfl
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem im_mk (x y : E) : (mk x y).im = y := rfl
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem mk_re_im (z : HilbertComplexification E) : mk z.re z.im = z := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem re_zero : (0 : HilbertComplexification E).re = 0 := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem im_zero : (0 : HilbertComplexification E).im = 0 := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem re_add (z w : HilbertComplexification E) : (z + w).re = z.re + w.re := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem im_add (z w : HilbertComplexification E) : (z + w).im = z.im + w.im := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem re_neg (z : HilbertComplexification E) : (-z).re = -z.re := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem im_neg (z : HilbertComplexification E) : (-z).im = -z.im := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem re_sub (z w : HilbertComplexification E) : (z - w).re = z.re - w.re := rfl
omit [InnerProductSpace ℝ E] in
@[simp] theorem im_sub (z w : HilbertComplexification E) : (z - w).im = z.im - w.im := rfl

noncomputable instance : SMul ℂ (HilbertComplexification E) :=
  ⟨fun c z => mk (c.re • z.re - c.im • z.im) (c.im • z.re + c.re • z.im)⟩

@[simp]
theorem re_smul (c : ℂ) (z : HilbertComplexification E) :
    (c • z).re = c.re • z.re - c.im • z.im := rfl

@[simp]
theorem im_smul (c : ℂ) (z : HilbertComplexification E) :
    (c • z).im = c.im • z.re + c.re • z.im := rfl

noncomputable instance : Module ℂ (HilbertComplexification E) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by
    ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im,
      sub_smul, add_smul, smul_sub, smul_add, smul_smul] <;> abel
  smul_zero c := by ext <;> simp
  smul_add c z w := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add, smul_add] <;> abel
  add_smul c d z := by
    ext <;> simp only [re_smul, im_smul, Complex.add_re, Complex.add_im,
      re_add, im_add, add_smul] <;> abel
  zero_smul z := by ext <;> simp

/-- Real scalar multiplication is the restriction of the constructed
complex action; these coordinate lemmas avoid a second real module instance. -/
@[simp]
theorem re_real_smul (r : ℝ) (z : HilbertComplexification E) :
    (r • z).re = r • z.re := by
  change ((r : ℂ) • z).re = _
  simp only [re_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

@[simp]
theorem im_real_smul (r : ℝ) (z : HilbertComplexification E) :
    (r • z).im = r • z.im := by
  change ((r : ℂ) • z).im = _
  simp only [im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

omit [InnerProductSpace ℝ E] in
theorem norm_sq (z : HilbertComplexification E) :
    ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 z

theorem norm_sq_inner (z : HilbertComplexification E) :
    ‖z‖ ^ 2 = inner ℝ z.re z.re + inner ℝ z.im z.im := by
  rw [norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem norm_complex_smul_sq (c : ℂ) (z : HilbertComplexification E) :
    ‖c • z‖ ^ 2 = (‖c‖ * ‖z‖) ^ 2 := by
  rw [mul_pow, norm_sq_inner, norm_sq_inner]
  simp only [re_smul, im_smul, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

noncomputable instance : NormedSpace ℂ (HilbertComplexification E) where
  norm_smul_le c z := by
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg c) (norm_nonneg z))
    simpa only [pow_two] using (le_of_eq (norm_complex_smul_sq c z))

/-- The Hermitian inner product, conjugate-linear in its first argument. -/
def complexInner (z w : HilbertComplexification E) : ℂ :=
  ⟨inner ℝ z.re w.re + inner ℝ z.im w.im,
    inner ℝ z.re w.im - inner ℝ z.im w.re⟩

noncomputable instance : InnerProductSpace ℂ (HilbertComplexification E) where
  inner := complexInner
  norm_sq_eq_re_inner z := norm_sq_inner z
  conj_inner_symm z w := by
    apply Complex.ext <;> simp [complexInner, real_inner_comm]
  add_left z w v := by
    apply Complex.ext <;> simp [complexInner, inner_add_left] <;> ring
  smul_left z w c := by
    apply Complex.ext <;>
      simp [complexInner, inner_sub_left, inner_add_left, real_inner_smul_left,
        Complex.mul_re, Complex.mul_im] <;> ring

theorem inner_eq (z w : HilbertComplexification E) :
    inner ℂ z w =
      ⟨inner ℝ z.re w.re + inner ℝ z.im w.im,
        inner ℝ z.re w.im - inner ℝ z.im w.re⟩ := rfl

/-- Completeness is inherited from the L² product, with its unchanged norm. -/
noncomputable instance [CompleteSpace E] : CompleteSpace (HilbertComplexification E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

/-- Explicit comparison with the original real L² product. The real
scalar actions agree by theorem, not by a duplicate module instance. -/
noncomputable def realEquiv : HilbertComplexification E ≃ₗᵢ[ℝ] WithLp 2 (E × E) where
  toFun z := WithLp.toLp 2 (z.re, z.im)
  invFun z := mk z.fst z.snd
  left_inv z := rfl
  right_inv z := rfl
  map_add' z w := rfl
  map_smul' r z := by
    apply WithLp.ofLp_injective 2
    change ((r • z).re, (r • z).im) = (r • z.re, r • z.im)
    rw [re_real_smul, im_real_smul]
  norm_map' z := rfl

/-- The canonical real isometric embedding. -/
noncomputable def ofReal : E →ₗᵢ[ℝ] HilbertComplexification E where
  toFun x := mk x 0
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq]
    simp

@[simp] theorem ofReal_re (x : E) : (ofReal x).re = x := rfl
@[simp] theorem ofReal_im (x : E) : (ofReal x).im = 0 := rfl

theorem eq_ofReal_add_I_smul (z : HilbertComplexification E) :
    z = ofReal z.re + Complex.I • ofReal z.im := by
  ext <;> simp

end HilbertComplexification
end VacuumBellSeparation.Gaussian
