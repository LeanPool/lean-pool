/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.CubeComparison
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# SolenoidalStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the antisymmetric-stream layer of `l.approximation.stationary.by.local` (ii)

ABK26, proof of part (ii) of `l.approximation.stationary.by.local`, builds its
competitor as the row divergence of a *cutoff antisymmetric tensor field*,

`j_{K,L,i} := Σ_m ∂_m ( η_{K,L} (S_{im} − (S_{im})_{cu_K}) )`,

and then asserts in one sentence: "Since the matrix field
`η_{K,L}(S − (S)_{cu_K})` is anti-symmetric and compactly supported in `cu_K`, we
have `j_{K,L} ∈ L²_{sol,0}(cu_K)`".

This file proves that sentence, unconditionally and at the level of an
arbitrary domain: `isSolenoidalZeroNormalTraceOn_streamDivergence` below.  In
CoarseGraining's vocabulary `L²_{sol,0}(U)` is `IsSolenoidalZeroNormalTraceOn
U`, i.e. exactly the manuscript's own definition `L²_{sol,0}(U) =
L²_{pot}(U)^⊥`: orthogonality to `∇H¹(U)`.  The proof is the double
integration by parts

`Σ_{i,m} ∫_U ∂_m T_{im} ∂_i φ = − Σ_{i,m} ∫_U φ ∂_i ∂_m T_{im} = 0`,

the last equality by Clairaut symmetry together with `T_{im} = −T_{mi}`.  No
probability, no stationarity, no sublinearity and no ergodic-theoretic input
enters; the only hypotheses are smoothness, compact support inside `U`, and
antisymmetry.

The second half of the file records the *converse* constraint on the same space,
which is what fixes the hypotheses part (ii) can legitimately be stated under.
Testing `IsSolenoidalZeroNormalTraceOn U g` against the affine `H¹(U)` functions
gives `∫_U g_i = 0` for every coordinate
(`setIntegral_coord_eq_zero_of_isSolenoidalZeroNormalTraceOn`), hence every
member of `L²_{sol,0}(U)` is orthogonal to the constant fields and

`∫_U |c − g|² ≥ |c|² |U|`  for every constant `c`

(`setIntegral_normSq_const_sub_ge`).  Part (ii) therefore requires a hypothesis
on `j` beyond solenoidality; see the module docstring of
`Algsuperdiff/Section3/Provider/Corrector/DirichletLowerBound.lean` for the
status of the node.

**Disclosure.**  Nothing in this file realizes any source node.  It proves the
membership step of part (ii) and an obstruction to part (ii); it does not prove
part (ii), and it claims no node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

variable {d : ℕ}

/-! ### Coordinate derivatives of a scalar field -/

/-- The `m`-th coordinate partial derivative of a scalar field on `ℝᵈ`. -/
def coordDeriv (f : Vec d → ℝ) (m : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ f x (basisVec m)

theorem coordDeriv_neg (f : Vec d → ℝ) (m : Fin d) :
    coordDeriv (-f) m = -coordDeriv f m := by
  funext x
  simp [coordDeriv, fderiv_neg]

/-- A coordinate derivative of a smooth field is smooth. -/
theorem contDiff_coordDeriv {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordDeriv f m) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
    have := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    simpa using this
  exact hd.clm_apply contDiff_const

/-- A coordinate derivative of a compactly supported field is compactly
supported. -/
theorem hasCompactSupport_coordDeriv {f : Vec d → ℝ} (hf : HasCompactSupport f)
    (m : Fin d) : HasCompactSupport (coordDeriv f m) :=
  hf.fderiv_apply ℝ (basisVec m)

/-- A coordinate derivative does not enlarge the closed support. -/
theorem tsupport_coordDeriv_subset (f : Vec d → ℝ) (m : Fin d) :
    tsupport (coordDeriv f m) ⊆ tsupport f := by
  refine le_trans (closure_mono ?_) (tsupport_fderiv_subset ℝ (f := f))
  intro x hx
  simp only [Function.mem_support, coordDeriv, ne_eq] at hx
  simp only [Function.mem_support, ne_eq]
  intro hzero
  exact hx (by simp [hzero])

/-! ### Clairaut symmetry in coordinate form -/

/-- The iterated coordinate derivative expressed through the second
Fréchet derivative. -/
theorem coordDeriv_coordDeriv_eq {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (m i : Fin d) (x : Vec d) :
    coordDeriv (coordDeriv f m) i x =
      fderiv ℝ (fderiv ℝ f) x (basisVec i) (basisVec m) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
    have := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    simpa using this
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hd.differentiable (by simp)).differentiableAt
  have hkey :
      fderiv ℝ (fun y => (fderiv ℝ f y) (basisVec m)) x =
        (fderiv ℝ f x).comp (fderiv ℝ (fun _ : Vec d => basisVec m) x) +
          (fderiv ℝ (fderiv ℝ f) x).flip (basisVec m) :=
    fderiv_clm_apply hdiff (differentiableAt_const _)
  have : coordDeriv (coordDeriv f m) i x =
      fderiv ℝ (fun y => (fderiv ℝ f y) (basisVec m)) x (basisVec i) := rfl
  rw [this, hkey]
  simp

/-- **Clairaut symmetry**: coordinate derivatives of a smooth field commute. -/
theorem coordDeriv_coordDeriv_comm {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (m i : Fin d) (x : Vec d) :
    coordDeriv (coordDeriv f m) i x = coordDeriv (coordDeriv f i) m x := by
  have hle : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField,
      show ((2 : WithTop ℕ∞)) = ((2 : ℕ∞) : WithTop ℕ∞) by norm_cast]
    exact WithTop.coe_le_coe.2 le_top
  have hsymm : IsSymmSndFDerivAt ℝ f x := (hf.contDiffAt).isSymmSndFDerivAt hle
  rw [coordDeriv_coordDeriv_eq hf, coordDeriv_coordDeriv_eq hf]
  exact hsymm.eq _ _

/-! ### The row divergence of a matrix field -/

/-- The row divergence of a matrix field `T = (T_{im})`, i.e. the vector field
`x ↦ (Σ_m ∂_m T_{im}(x))_i`.  This is the manuscript's `j_{K,L}` once `T` is the
cutoff antisymmetric stream tensor. -/
def streamDivergence (T : Fin d → Fin d → (Vec d → ℝ)) (x : Vec d) : Vec d :=
  fun i => ∑ m : Fin d, coordDeriv (T i m) m x

theorem streamDivergence_apply (T : Fin d → Fin d → (Vec d → ℝ)) (x : Vec d)
    (i : Fin d) :
    streamDivergence T x i = ∑ m : Fin d, coordDeriv (T i m) m x := rfl

/-! ### Membership of the row divergence in `L²_{sol,0}(U)` -/

section Membership

variable {U : Set (Vec d)} {T : Fin d → Fin d → (Vec d → ℝ)}

/-- Square integrability on `U` of a continuous compactly supported field. -/
theorem memScalarL2_of_continuous_of_hasCompactSupport {f : Vec d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemScalarL2 U f :=
  (hf.memLp_of_hasCompactSupport (μ := volume) (p := 2) hfc).restrict U

/-- The pairing of an `L²` coordinate against a continuous compactly supported
field is integrable. -/
theorem integrableOn_mul_of_memScalarL2 {u f : Vec d → ℝ} (hu : MemScalarL2 U u)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => u x * f x) U := by
  have := hu.integrable_mul
    (memScalarL2_of_continuous_of_hasCompactSupport (U := U) hf hfc)
  simpa [IntegrableOn, Pi.mul_apply] using! this

/-- The single integration by parts against an `H¹(U)` test function:
`∫_U (∇φ)_i ∂_m T_{im} = − ∫_U φ ∂_i ∂_m T_{im}`. -/
theorem setIntegral_grad_mul_coordDeriv_eq (φ : H1Function U)
    (hsmooth : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (T i m))
    (hsupp : ∀ i m, HasCompactSupport (T i m))
    (hsub : ∀ i m, tsupport (T i m) ⊆ U) (i m : Fin d) :
    ∫ x in U, φ.grad x i * coordDeriv (T i m) m x =
      -∫ x in U, φ.toFun x * coordDeriv (coordDeriv (T i m) m) i x := by
  have hψ := hsmooth i m
  have hs : ContDiff ℝ (⊤ : ℕ∞) (coordDeriv (T i m) m) := contDiff_coordDeriv hψ m
  have hc : HasCompactSupport (coordDeriv (T i m) m) :=
    hasCompactSupport_coordDeriv (hsupp i m) m
  have hsu : tsupport (coordDeriv (T i m) m) ⊆ U :=
    le_trans (tsupport_coordDeriv_subset (T i m) m) (hsub i m)
  have hweak := φ.hasWeakGradient i (coordDeriv (T i m) m) hs hc hsu
  have hweak' : ∫ x in U, φ.toFun x * coordDeriv (coordDeriv (T i m) m) i x
      = -∫ x in U, φ.grad x i * coordDeriv (T i m) m x := by
    simpa [coordDeriv] using hweak
  linarith [hweak']

/-- **The membership step of `l.approximation.stationary.by.local` (ii)**.

If `T = (T_{im})` is a smooth antisymmetric matrix field whose entries are
compactly supported inside `U`, then its row divergence
`x ↦ (Σ_m ∂_m T_{im}(x))_i` lies in `L²_{sol,0}(U)`, i.e. it is orthogonal to
`∇H¹(U)`.

Only smoothness, compact support in `U` and antisymmetry are used. -/
theorem isSolenoidalZeroNormalTraceOn_streamDivergence
    (hsmooth : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (T i m))
    (hsupp : ∀ i m, HasCompactSupport (T i m))
    (hsub : ∀ i m, tsupport (T i m) ⊆ U)
    (hanti : ∀ i m, T m i = -T i m) :
    IsSolenoidalZeroNormalTraceOn U (streamDivergence T) := by
  intro φ
  classical
  -- the second-derivative pairings, antisymmetric in the index pair
  set b : Fin d → Fin d → ℝ := fun i m =>
    ∫ x in U, φ.toFun x * coordDeriv (coordDeriv (T i m) m) i x with hbdef
  have hbanti : ∀ i m, b m i = -b i m := by
    intro i m
    have hpt : ∀ x : Vec d,
        coordDeriv (coordDeriv (T m i) i) m x =
          -coordDeriv (coordDeriv (T i m) m) i x := by
      intro x
      have h1 : coordDeriv (T m i) i = -coordDeriv (T i m) i := by
        rw [hanti i m, coordDeriv_neg]
      rw [h1, coordDeriv_neg]
      simp only [Pi.neg_apply, neg_inj]
      exact coordDeriv_coordDeriv_comm (hsmooth i m) i m x
    have hfun : (fun x => φ.toFun x * coordDeriv (coordDeriv (T m i) i) m x) =
        fun x => -(φ.toFun x * coordDeriv (coordDeriv (T i m) m) i x) := by
      funext x
      rw [hpt x]
      ring
    simp only [hbdef]
    rw [hfun, integral_neg]
  -- the double sum of an antisymmetric array vanishes
  have hsum : ∑ i : Fin d, ∑ m : Fin d, b i m = 0 := by
    have hswap : ∑ i : Fin d, ∑ m : Fin d, b i m
        = ∑ i : Fin d, ∑ m : Fin d, b m i := Finset.sum_comm
    have hneg : ∑ i : Fin d, ∑ m : Fin d, b m i
        = -∑ i : Fin d, ∑ m : Fin d, b i m := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => hbanti i m
    have := hswap.trans hneg
    linarith
  -- integrability of every summand
  have hint : ∀ i m : Fin d,
      IntegrableOn (fun x => φ.grad x i * coordDeriv (T i m) m x) U := by
    intro i m
    exact integrableOn_mul_of_memScalarL2 (φ.grad_memL2 i)
      ((contDiff_coordDeriv (hsmooth i m) m).continuous)
      (hasCompactSupport_coordDeriv (hsupp i m) m)
  -- expand the pairing and integrate term by term
  have hexpand : ∀ x : Vec d, vecDot (streamDivergence T x) (φ.grad x) =
      ∑ i : Fin d, ∑ m : Fin d, φ.grad x i * coordDeriv (T i m) m x := by
    intro x
    simp only [vecDot, streamDivergence_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  calc ∫ x in U, vecDot (streamDivergence T x) (φ.grad x)
      = ∫ x in U, ∑ i : Fin d, ∑ m : Fin d, φ.grad x i * coordDeriv (T i m) m x := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => hexpand x)
    _ = ∑ i : Fin d, ∑ m : Fin d,
          ∫ x in U, φ.grad x i * coordDeriv (T i m) m x := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun m _ => hint i m)]
        exact Finset.sum_congr rfl fun i _ =>
          integral_finsetSum _ fun m _ => hint i m
    _ = ∑ i : Fin d, ∑ m : Fin d, -b i m := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
        exact setIntegral_grad_mul_coordDeriv_eq φ hsmooth hsupp hsub i m
    _ = -∑ i : Fin d, ∑ m : Fin d, b i m := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_neg_distrib]
    _ = 0 := by rw [hsum, neg_zero]

end Membership

/-! ### The cutoff stream tensor and its row divergence -/

section Cutoff

variable {U : Set (Vec d)} {η : Vec d → ℝ} {S : Fin d → Fin d → (Vec d → ℝ)}
variable {c : Fin d → Fin d → ℝ}

/-- The manuscript's cutoff stream tensor `η_{K,L}(S − (S)_{cu_K})`, with the
cube averages entered as an arbitrary constant matrix `c`. -/
def cutoffStream (η : Vec d → ℝ) (S : Fin d → Fin d → (Vec d → ℝ))
    (c : Fin d → Fin d → ℝ) (i m : Fin d) (x : Vec d) : ℝ :=
  η x * (S i m x - c i m)

/-- The Leibniz rule for a coordinate derivative of a product. -/
theorem coordDeriv_mul {f g : Vec d → ℝ} {x : Vec d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (m : Fin d) :
    coordDeriv (fun y => f y * g y) m x
      = coordDeriv f m x * g x + f x * coordDeriv g m x := by
  simp only [coordDeriv, fderiv_fun_mul hf hg]
  simp only [add_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- The coordinate derivative ignores an additive constant. -/
theorem coordDeriv_sub_const (f : Vec d → ℝ) (a : ℝ) (m : Fin d) (x : Vec d) :
    coordDeriv (fun y => f y - a) m x = coordDeriv f m x := by
  simp only [coordDeriv]
  rw [fderiv_sub_const]

/-- **The product-rule decomposition of the cutoff competitor**.  The row
divergence of the cutoff stream tensor splits into the cutoff of the row
divergence of `S` and the remainder built from `∇η`. -/
theorem streamDivergence_cutoffStream_apply {x : Vec d}
    (hη : DifferentiableAt ℝ η x) (hS : ∀ i m, DifferentiableAt ℝ (S i m) x)
    (i : Fin d) :
    streamDivergence (cutoffStream η S c) x i
      = η x * streamDivergence S x i
        + ∑ m : Fin d, coordDeriv η m x * (S i m x - c i m) := by
  classical
  have hterm : ∀ m : Fin d,
      coordDeriv (cutoffStream η S c i m) m x
        = η x * coordDeriv (S i m) m x
          + coordDeriv η m x * (S i m x - c i m) := by
    intro m
    have hsub : DifferentiableAt ℝ (fun y => S i m y - c i m) x :=
      (hS i m).sub_const _
    have := coordDeriv_mul (f := η) (g := fun y => S i m y - c i m) hη hsub m
    rw [coordDeriv_sub_const] at this
    simpa [cutoffStream] using! this.trans (by ring)
  simp only [streamDivergence_apply]
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib,
    ← Finset.mul_sum]

/-- **The cutoff competitor is admissible**: the row divergence of `η (S − c)`
lies in `L²_{sol,0}(U)` whenever `η` is smooth and compactly supported in `U`
and both `S` and `c` are antisymmetric.  This is the manuscript's sentence in
ABK26, in the form in which part (ii) uses it. -/
theorem isSolenoidalZeroNormalTraceOn_cutoffStream
    (hηs : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ U)
    (hS : ∀ i m, ContDiff ℝ (⊤ : ℕ∞) (S i m))
    (hSanti : ∀ i m, S m i = -S i m) (hcanti : ∀ i m, c m i = -c i m) :
    IsSolenoidalZeroNormalTraceOn U (streamDivergence (cutoffStream η S c)) := by
  refine isSolenoidalZeroNormalTraceOn_streamDivergence ?_ ?_ ?_ ?_
  · intro i m
    exact hηs.mul ((hS i m).sub contDiff_const)
  · intro i m
    exact hηc.mul_right
  · intro i m
    exact le_trans (tsupport_mul_subset_left (f := η)
      (g := fun x => S i m x - c i m)) hηsub
  · intro i m
    funext x
    have hS' : S m i x = -S i m x := by rw [hSanti i m]; rfl
    have hc' : c m i = -c i m := hcanti i m
    simp only [cutoffStream, Pi.neg_apply, hS', hc']
    ring

end Cutoff

section Obstruction

variable {U : Set (Vec d)}

end Obstruction

end

end Algsuperdiff.Section3.Provider.Corrector
