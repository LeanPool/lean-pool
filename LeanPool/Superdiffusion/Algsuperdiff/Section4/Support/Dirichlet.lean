/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.Definitions

/-!
# Dirichlet

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Section 4 deterministic carriers: Dirichlet problems, Hölder and fractional gauges

The definitional layer beneath the §4.3 anchors
(`l.harmonic.approximation.good.scales`) and beneath the two roots'
deterministic clauses (`t.homogenization`; `t.regularity`).  Everything here
is stated over the CoarseGraining carriers `Vec d`, `H1Function`,
`H10Function`, `CoeffField`, `TriadicCube`; no Section 3 probabilistic object
appears, and no estimate is proved.

## The Dirichlet carrier (frozen-surface resolution A7)

The manuscript's

```text
  -∇ · a ∇u = ∇ · g   in □_m ,        u = h  on ∂□_m
```

*Sign convention.*  `IsDivFormWeakSolutionOn` renders `-∇·a∇u = ∇·g` in the
standard distributional convention `⟪∇·g, φ⟫ = -∫ g·∇φ`, i.e. with the minus
sign on the right of the weak identity.  CoarseGraining's
`Homogenization.IsZeroTraceDirichletRhsWeakSolution` carries the same equation
with the opposite convention for `∇·g` (its weak identity has no minus sign),
so the two predicates correspond at the *negated* forcing.  The frozen §4.3
statement quantifies universally over the pair `(u, g)` and bounds the right
side by *seminorms* of `g`, both invariant under `g ↦ -g`, so the statement
itself does not depend on which of the two conventions is fixed.

## The Hölder carrier

The `p = ∞` fractional slots `[g]_{W^{1/2,∞}}` and `‖∇h‖_{W^{1/2,∞}}` are
carried at the Hölder seminorm `C^{0,α}` in explicit bound-predicate form,
following ABK26 ("`[·]_{C^{0,s}}` and
`[·]_{W^{s,∞}}` are equivalent up to dimensional constants on a cube; we use
them interchangeably").
`HolderSeminormBoundOn U α K f` is the plain `[f]_{C^{0,α}(U)} ≤ K` bound.

## The fractional carrier

`[u]_{W^{s,p}(U)}` is defined by *one* normalized integral,

```text
  [u]_{W^{s,p}(U)} = ( ⨍_U ∫_U |u(x) - u(y)|^p / |x-y|^{d+sp} dx dy )^{1/p} ,
```

which is exactly CoarseGraining's `Gagliardo.cubeGagliardoESeminorm` when `U` is
a triadic cube (normalized product measure in the first slot, plain restricted
volume in the second).  §4.3 needs the same object on the *intersection*
windows `(x+□_{n+1}) ∩ □_m`, which are not triadic cubes, so the normalized
measure is rebuilt here for an arbitrary set and the cube case is proved to
agree with CoarseGraining's (`normalizedGagliardo).  CoarseGraining's
unnormalized `gagliardo uses the plain restricted volume in *both* slots and is
therefore not the tex's object.

*Metric convention.*  CoarseGraining's `Gagliardo.gagliardoKernel` measures `|x
- y|` in the ambient `Vec d` norm, which is the supremum norm on `Fin d → ℝ`,
not the manuscript's Euclidean norm (CoarseGraining records this deviation in
its own module docstring; the two differ by a factor at most `d^{(d+sp)/2}` on
the kernel, absorbed in the dimensional constants).  `HolderSeminormBoundOn`
uses the same ambient norm, so the two `p = ∞` and `p = 2` carriers of this
file are stated in one metric.

## Main definitions

* `IsWeaklyHarmonicOn W v` — `∫_W ∇v · ∇φ = 0` for all `φ ∈ H¹₀(W)`.
* `IsDivFormWeakSolutionOn a W u g` — the divergence-form weak equation.
* `HasZeroTraceDifferenceOn W u h` — `u - h ∈ H¹₀(W)`, with witness.
* `IsDirichletSolutionOn a Q u h g` — the A7 rendering of the tex's problem.
* `HolderSeminormBoundOn U α K f`, `MemHolder U α f` — the `C^{0,α}` carriers.
* `normalizedGagliardo A s f` — the tex's `[f]_{H^s(A)}` on an arbitrary
  finite-volume set.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
* ABK26, the function-space conventions and the fractional Sobolev seminorm.
-/

namespace Algsuperdiff.Section4.Support

open MeasureTheory
open HCPolySupport
open scoped ENNReal

variable {d : ℕ}

/-! ## 1. Weak harmonicity -/

/-- **Weak harmonicity** of an `H¹` function on `W`: the first variation of the
Dirichlet energy vanishes against every zero-trace test function,
`∫_W ∇v · ∇φ = 0` for all `φ ∈ H¹₀(W)`.

This is `-Δ v = 0` in `W` in the variational sense — the interior half of the
tex's Dirichlet problem `e.harmonic.approx.v.def`. -/
def IsWeaklyHarmonicOn (W : Set (Vec d)) (v : H1Function W) : Prop :=
  ∀ φ : H10Function W,
    ∫ x in W, vecDot (v.grad x) (φ.toH1Function.grad x) ∂volume = 0

/-! ## 2. Divergence-form weak solutions and the Dirichlet carrier -/

/-- **The divergence-form weak equation** `-∇ · a ∇u = ∇ · g` on `W`, tested
against `H¹₀(W)`:

`∫_W (a ∇u) · ∇φ = - ∫_W g · ∇φ`  for all `φ ∈ H¹₀(W)`.

The minus sign is the standard distributional convention `⟪∇·g, φ⟫ = -∫ g·∇φ`;
see the module docstring for the correspondence with CoarseGraining's
`IsZeroTraceDirichletRhsWeakSolution`, which fixes the opposite convention. -/
def IsDivFormWeakSolutionOn (a : CoeffField d) (W : Set (Vec d))
    (u : H1Function W) (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function W,
    ∫ x in W, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) ∂volume =
      -∫ x in W, vecDot (g x) (φ.toH1Function.grad x) ∂volume

theorem isDivFormWeakSolutionOn_def {a : CoeffField d} {W : Set (Vec d)}
    {u : H1Function W} {g : Vec d → Vec d} :
    IsDivFormWeakSolutionOn a W u g ↔
      ∀ φ : H10Function W,
        ∫ x in W, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) ∂volume =
          -∫ x in W, vecDot (g x) (φ.toH1Function.grad x) ∂volume :=
  Iff.rfl

def HasZeroTraceDifferenceOn (W : Set (Vec d)) (u h : H1Function W) : Prop :=
  ∃ w : H10Function W,
    (∀ x, u.toFun x = h.toFun x + w.toH1Function.toFun x) ∧
      ∀ x, u.grad x = h.grad x + w.toH1Function.grad x

/-- **The §4.3 Dirichlet problem**:

```text
  u ∈ H¹(□) ,   -∇ · a ∇u = ∇ · g  in □ ,   u = h  on ∂□ ,
```

read as: `u - h` is realized in `H¹₀(□)` and `u` satisfies the divergence-form
weak equation against `H¹₀(□)` tests.  `□` is the *open* realization
`openCubeSet Q` of the triadic cube, the domain on which CoarseGraining's
analytic lemmas are stated. -/
def IsDirichletSolutionOn (a : CoeffField d) (Q : TriadicCube d)
    (u h : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Prop :=
  HasZeroTraceDifferenceOn (openCubeSet Q) u h ∧
    IsDivFormWeakSolutionOn a (openCubeSet Q) u g

theorem IsDirichletSolutionOn.hasZeroTraceDifferenceOn {a : CoeffField d} {Q : TriadicCube d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionOn a Q u h g) :
    HasZeroTraceDifferenceOn (openCubeSet Q) u h :=
  hu.1

theorem IsDirichletSolutionOn.isDivFormWeakSolutionOn {a : CoeffField d} {Q : TriadicCube d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionOn a Q u h g) :
    IsDivFormWeakSolutionOn a (openCubeSet Q) u g :=
  hu.2

/-! ### The CoarseGraining compatibility anchor -/

private theorem vecDot_neg_left (x y : Vec d) : vecDot (-x) y = -vecDot x y := by
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem integral_vecDot_neg_left {W : Set (Vec d)} (g p : Vec d → Vec d) :
    ∫ x in W, vecDot (-g x) (p x) ∂volume = -∫ x in W, vecDot (g x) (p x) ∂volume := by
  simp only [vecDot_neg_left, integral_neg]

/-- **Compatibility with the CoarseGraining Dirichlet surface.**

If the gradient of `u` is the gradient of a zero-trace function `w` — in
particular when `u = h + w` with `h` of vanishing gradient, the zero boundary
datum — then the divergence-form weak equation for `u` at forcing `g` is
exactly CoarseGraining's `IsZeroTraceDirichletRhsWeakSolution` for `w` at
forcing `-g`.

The negation is the sign-convention correspondence recorded in the module
docstring: CoarseGraining's predicate carries `-∇·a∇u = ∇·g` with the weak
identity `∫ a∇u·∇φ = ∫ g·∇φ`, this file with `∫ a∇u·∇φ = -∫ g·∇φ`. -/
theorem isZeroTraceDirichletRhsWeakSolution_iff_isDivFormWeakSolutionOn
    {a : CoeffField d} {W : Set (Vec d)} {u : H1Function W} {w : H10Function W}
    {g : Vec d → Vec d} (hgrad : ∀ x, u.grad x = w.toH1Function.grad x) :
    IsZeroTraceDirichletRhsWeakSolution a W w (fun x => -g x) ↔
      IsDivFormWeakSolutionOn a W u g := by
  unfold IsZeroTraceDirichletRhsWeakSolution IsDivFormWeakSolutionOn
  simp only [hgrad, integral_vecDot_neg_left]

/-! ## 3. The Hölder carrier -/

variable {E : Type*} [NormedAddCommGroup E]

/-- **`[f]_{C^{0,α}(U)} ≤ K`** in explicit bound-predicate form: `|f(x) - f(y)| ≤ K
|x - y|^α` for all `x, y ∈ U`.

The volume/scale normalization of `W^{α,∞}` is **not** folded in and must be
supplied by the consuming statement.

`|·|` is the ambient norm of `Vec d`, the supremum norm — the same metric
CoarseGraining's `Gagliardo.gagliardoKernel` uses; the manuscript's Euclidean
norm differs by a dimensional factor. -/
def HolderSeminormBoundOn (U : Set (Vec d)) (alpha K : ℝ) (f : Vec d → E) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha

theorem holderSeminormBoundOn_def {U : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E} :
    HolderSeminormBoundOn U alpha K f ↔
      ∀ x ∈ U, ∀ y ∈ U, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha :=
  Iff.rfl

/-- The bound is monotone in the constant. -/
theorem HolderSeminormBoundOn.mono_const {U : Set (Vec d)} {alpha K K' : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn U alpha K f) (hKK : K ≤ K') :
    HolderSeminormBoundOn U alpha K' f := by
  intro x hx y hy
  refine (hf x hx y hy).trans ?_
  exact mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (norm_nonneg _) alpha)

/-- The bound is monotone (decreasing) in the domain. -/
theorem HolderSeminormBoundOn.mono_set {U V : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn U alpha K f) (hVU : V ⊆ U) :
    HolderSeminormBoundOn V alpha K f :=
  fun x hx y hy => hf x (hVU hx) y (hVU hy)

/-- A Hölder bound holding at two distinct points of `U` forces the constant to
be nonnegative. -/
theorem HolderSeminormBoundOn.nonneg {U : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn U alpha K f) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : x ≠ y) : 0 ≤ K := by
  have hpos : (0 : ℝ) < ‖x - y‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero_of_ne hxy
  have hrpos : (0 : ℝ) < ‖x - y‖ ^ alpha := Real.rpow_pos_of_pos hpos alpha
  by_contra hK
  push Not at hK
  have hneg : K * ‖x - y‖ ^ alpha < 0 := mul_neg_of_neg_of_pos hK hrpos
  have hle := hf x hx y hy
  have h0 : (0 : ℝ) ≤ ‖f x - f y‖ := norm_nonneg _
  linarith only [hneg, hle, h0]

/-- The zero field satisfies every nonnegative Hölder bound. -/
theorem holderSeminormBoundOn_zero (U : Set (Vec d)) (alpha : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    HolderSeminormBoundOn U alpha K (fun _ => (0 : E)) := by
  intro x _ y _
  have h0 : ‖(0 : E) - (0 : E)‖ = 0 := by simp
  rw [h0]
  exact mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) alpha)

/-! ## 4. The volume-normalized fractional (Gagliardo) gauge -/

variable [NormedSpace ℝ E]

/-- `⨍_A`, the volume-normalized restriction of Lebesgue measure to `A`.  On a
triadic cube this is CoarseGraining's `normalizedCubeMeasure`
(`normalizedVolumeMeasureOn_cubeSet`). -/
noncomputable def normalizedVolumeMeasureOn (A : Set (Vec d)) : Measure (Vec d) :=
  (volume A)⁻¹ • volume.restrict A

theorem normalizedVolumeMeasureOn_def (A : Set (Vec d)) :
    normalizedVolumeMeasureOn A = (volume A)⁻¹ • volume.restrict A :=
  rfl

theorem normalizedVolumeMeasureOn_cubeSet (Q : TriadicCube d) :
    normalizedVolumeMeasureOn (cubeSet Q) = normalizedCubeMeasure Q := by
  have hvol : volume (cubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [← cubeMeasure_apply_univ Q]
    exact cubeMeasure_apply_univ_eq Q
  rw [normalizedVolumeMeasureOn, normalizedCubeMeasure, cubeMeasure, hvol,
    ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]

/-- The manuscript's `⨍_A ∫_A` normalization as a product measure: normalized in
the first variable, plain restricted volume in the second — CoarseGraining's
`Gagliardo.gagliardoCubeMeasure` construction on an arbitrary set. -/
noncomputable def normalizedGagliardoMeasureOn (A : Set (Vec d)) : Measure (Vec d × Vec d) :=
  (normalizedVolumeMeasureOn A).prod (volume.restrict A)

theorem normalizedGagliardoMeasureOn_def (A : Set (Vec d)) :
    normalizedGagliardoMeasureOn A = (normalizedVolumeMeasureOn A).prod (volume.restrict A) :=
  rfl

theorem normalizedGagliardoMeasureOn_cubeSet (Q : TriadicCube d) :
    normalizedGagliardoMeasureOn (cubeSet Q) = Gagliardo.gagliardoCubeMeasure Q := by
  rw [normalizedGagliardoMeasureOn, Gagliardo.gagliardoCubeMeasure,
    normalizedVolumeMeasureOn_cubeSet, cubeMeasure]

/-- **`[f]_{H^s(A)}`**, the manuscript's volume-normalized fractional Sobolev
seminorm at `p = 2` on an arbitrary set `A`:

```text
  [f]_{H^s(A)} = ( ⨍_A ∫_A |f(x) - f(y)|² / |x-y|^{d+2s} dx dy )^{1/2} ,
```

`ℝ≥0∞`-valued, with CoarseGraining's difference-quotient kernel.

The definition is generic in the target `E`, so the scalar leg `‖∇h‖_{H^s}`
(`E := ℝ`) and the vector leg `[g]_{H^s}` (`E := Vec d`, whose norm is the
ambient supremum norm) are instances of one declaration. -/
noncomputable def normalizedGagliardoESeminormOn (A : Set (Vec d)) (s : ℝ)
    (f : Vec d → E) : ℝ≥0∞ :=
  eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2 (normalizedGagliardoMeasureOn A)

theorem normalizedGagliardoESeminormOn_def (A : Set (Vec d)) (s : ℝ) (f : Vec d → E) :
    normalizedGagliardoESeminormOn A s f =
      eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2 (normalizedGagliardoMeasureOn A) :=
  rfl

end Algsuperdiff.Section4.Support
