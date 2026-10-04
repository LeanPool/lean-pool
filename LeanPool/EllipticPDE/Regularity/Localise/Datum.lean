/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Localise.LocalOp
public import LeanPool.EllipticPDE.Regularity.InteriorSmooth
public import Mathlib.Data.Set.Finite.List


/-!
# The datum bridge and the localisation of a local weak solution

`interior_smooth` asks for a datum `f : L2D Ω` with weak derivatives of every order in `L²(Ω)`,
each bounded in `L²`, and for the equation to hold in the weak sense against every `w ∈ H01 Ω`.
Evans §6.3.1, Theorem 3 hypothesises a datum smooth on `Ω` and a solution posed only locally,
against test functions compactly supported in the region rather than against every member of
`H01 Ω`. This file supplies both bridges.

* A smooth compactly supported function already has every weak derivative in `L²`, by its
  classical iterated partials (`iteratedWeakDerivOfContDiff`), so `datum_hyp` discharges the
  datum hypothesis of `interior_smooth` outright.
* `LocalWeakSol` states the local weak formulation on plain function representatives, tested
  only against functions compactly supported in the region. `localise` reduces a local weak
  solution of an equation with coefficients and datum smooth on `U`, near a compact `K ⊆ U`, to
  a local weak solution on a smaller open `W` of an equation with the global bounded-measurable
  coefficients `localOp` supplies and a smooth compactly supported datum, cut off from the
  original by the same cutoff.

Neither bridge touches the global weak formulation against every member of `H01 Ω`.
`Regularity/Local/WeakSolution.lean` connects `LocalWeakSol` to the predicate
`IsLocalWeakSolution` on the ambient space, through which `interior_smooth_W12` applies.

## Main declarations

* `toL2`, `iteratedWeakDerivOfContDiff`, `datum_hyp`: the datum bridge.
* `LocalWeakSol`: a local weak solution on plain representatives, with `congr`, `mono`.
* `localise`: the localisation step of Evans §6.3.1, Theorem 3.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Datum: a smooth compactly supported function has every weak derivative in `L²(Ω)` -/

/-- The topological support of an iterated classical partial of a compactly supported function
stays compactly supported: each `fderiv` step preserves compact support. -/
theorem hasCompactSupport_iterPartial {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : HasCompactSupport g) : ∀ α : List (Fin d), HasCompactSupport (iterPartial g α)
  | [] => hc
  | l :: α => (hasCompactSupport_iterPartial hc α).fderiv_apply (𝕜 := ℝ)
      (EuclideanSpace.single l 1)

/-- Every iterated classical partial of a `C^∞` function is itself smooth to every finite
order. -/
theorem contDiff_iterPartial_top {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (n : ℕ) (α : List (Fin d)) :
    ContDiff ℝ ((n : ℕ) : ℕ∞) (iterPartial g α) :=
  contDiff_iterPartial α (hg.of_le (by exact_mod_cast le_top))

/-- An iterated classical partial of a smooth compactly supported function lies in `L²` of any
region: it is continuous with compact support. -/
theorem memLp_iterPartial {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (Ω : Set (EuclideanSpace ℝ (Fin d))) (α : List (Fin d)) :
    MemLp (iterPartial g α) 2 (volume.restrict Ω) :=
  (contDiff_iterPartial_top hg 0 α).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_iterPartial hc α)

/-- The `L²(Ω)` class of a smooth compactly supported function. -/
def toL2 {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (Ω : Set (EuclideanSpace ℝ (Fin d))) : L2D Ω :=
  (memLp_iterPartial hg hc Ω []).toLp g

/-- **The datum bridge.** Classical iterated partials of a smooth compactly supported `g` are its
weak derivatives on any `Ω`, to every order: integration by parts against a test function
compactly supported in `Ω` reduces to the whole-space identity `hasWeakPartial_partialD`, since
both sides vanish off `Ω`. -/
def iteratedWeakDerivOfContDiff {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    HasIteratedWeakDerivOn Ω k (toL2 hg hc Ω) where
  D α := (memLp_iterPartial hg hc Ω α).toLp (iterPartial g α)
  D_nil := rfl
  D_step m α _ := by
    intro φ hφ hφc hφΩ
    have hφ0 : ∀ x ∉ Ω, φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hφΩ h))
    have hdφ0 : ∀ x ∉ Ω, partialD m φ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hφΩ (tsupport_partialD_subset m φ h)))
    calc ∫ x in Ω, ((memLp_iterPartial hg hc Ω α).toLp (iterPartial g α) x : ℝ)
            * partialD m φ x
        = ∫ x in Ω, iterPartial g α x * partialD m φ x := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_iterPartial hg hc Ω α).coeFn_toLp] with x hx
          rw [hx]
      _ = ∫ x, iterPartial g α x * partialD m φ x :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hdφ0 x hx]
      _ = - ∫ x, iterPartial g (m :: α) x * φ x :=
          hasWeakPartial_partialD (contDiff_iterPartial_top hg 1 α) m φ hφ hφc
      _ = - ∫ x in Ω, iterPartial g (m :: α) x * φ x := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hφ0 x hx]]
      _ = - ∫ x in Ω, ((memLp_iterPartial hg hc Ω (m :: α)).toLp (iterPartial g (m :: α)) x : ℝ)
            * φ x := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [(memLp_iterPartial hg hc Ω (m :: α)).coeFn_toLp] with x hx
          rw [hx]

/-- **The datum hypothesis of `interior_smooth`, discharged for a smooth compactly supported
datum, on any `Ω`.** The family of iterated classical partials has finitely many entries up to
each order, so their norms are bounded above. -/
theorem datum_hyp {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) :
    ∃ hfk : HasIteratedWeakDerivOn Ω k (toL2 hg hc Ω), ∃ M : ℝ, IteratedL2Bound hfk M := by
  refine ⟨iteratedWeakDerivOfContDiff hg hc Ω k, ?_⟩
  obtain ⟨M, hM⟩ := ((List.finite_length_le (Fin d) k).image
    (fun α => ‖(iteratedWeakDerivOfContDiff hg hc Ω k).D α‖)).bddAbove
  exact ⟨M, fun α hα => hM ⟨α, hα, rfl⟩⟩

/-- A datum smooth on `U`, cut off by a test function of `U`: the product is globally smooth and
compactly supported, ready for `datum_hyp`. -/
theorem datum_cutoff {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {χ f : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn U χ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * f x) ∧ HasCompactSupport (fun x => χ x * f x) :=
  ⟨contDiff_mul_of_contDiffOn hU hχ hf, hasCompactSupport_mul hχ⟩

/-! ### Local weak formulation and its transfer -/

/-- **Local weak solution on `W`, on plain function representatives.** `u` with gradient `G`,
tested against smooth functions compactly supported in `W`. This is the plain-integral shape
Evans §6.3.1 states the equation in, ahead of the `H01`-and-`fullBilin` formulation
`interior_smooth` asks for; `isLocalWeakSolution_iff_localWeakSol` connects it to the predicate
`IsLocalWeakSolution` on the ambient space. -/
def LocalWeakSol (W : Set (EuclideanSpace ℝ (Fin d)))
    (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ)
    (c f u : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ W →
    (∑ i, ∑ j, ∫ x in W, a x i j * G i x * partialD j φ x)
      + (∑ i, ∫ x in W, b x i * G i x * φ x) + (∫ x in W, c x * u x * φ x)
      = ∫ x in W, f x * φ x

/-- Coefficients and datum that agree on `W` give the same local weak formulation on `W`. -/
theorem LocalWeakSol.congr {W : Set (EuclideanSpace ℝ (Fin d))} (hW : MeasurableSet W)
    {a a' : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b b' : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c c' f f' u : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : ∀ x ∈ W, a x = a' x) (hb : ∀ x ∈ W, b x = b' x) (hc : ∀ x ∈ W, c x = c' x)
    (hf : ∀ x ∈ W, f x = f' x) (h : LocalWeakSol W a b c f u G) :
    LocalWeakSol W a' b' c' f' u G := by
  intro φ hφ hφc hφW
  have e := h φ hφ hφc hφW
  have e1 : ∀ i j, ∫ x in W, a x i j * G i x * partialD j φ x
      = ∫ x in W, a' x i j * G i x * partialD j φ x := fun i j =>
    setIntegral_congr_fun hW fun x hx => by simp only [ha x hx]
  have e2 : ∀ i, ∫ x in W, b x i * G i x * φ x = ∫ x in W, b' x i * G i x * φ x := fun i =>
    setIntegral_congr_fun hW fun x hx => by simp only [hb x hx]
  have e3 : ∫ x in W, c x * u x * φ x = ∫ x in W, c' x * u x * φ x :=
    setIntegral_congr_fun hW fun x hx => by simp only [hc x hx]
  have e4 : ∫ x in W, f x * φ x = ∫ x in W, f' x * φ x :=
    setIntegral_congr_fun hW fun x hx => by simp only [hf x hx]
  simp only [e1, e2, e3, e4] at e
  exact e

/-- A local weak solution on `W` is one on every `W' ⊆ W`: a test function compactly supported in
`W'` sees only `W'`. No measurability is asked of either set. -/
theorem LocalWeakSol.mono {W W' : Set (EuclideanSpace ℝ (Fin d))} (hW' : W' ⊆ W)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c f u : EuclideanSpace ℝ (Fin d) → ℝ} {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : LocalWeakSol W a b c f u G) : LocalWeakSol W' a b c f u G := by
  intro φ hφ hφc hφW'
  have e := h φ hφ hφc (hφW'.trans hW')
  have hφ0 : ∀ x ∉ W', φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφW' h))
  have hdφ0 : ∀ j, ∀ x ∉ W', partialD j φ x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφW' (tsupport_partialD_subset j φ h)))
  have tr : ∀ F : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x ∉ W', F x = 0) →
      ∫ x in W, F x = ∫ x in W', F x := fun F hF =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero
        fun x hx => hF x (fun h => hx (hW' h))).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      tr _ fun x hx => by simp [hdφ0 j x hx],
    Finset.sum_congr rfl fun i _ => tr _ fun x hx => by simp [hφ0 x hx],
    tr (fun x => c x * u x * φ x) fun x hx => by simp [hφ0 x hx],
    tr (fun x => f x * φ x) fun x hx => by simp [hφ0 x hx]] at e
  exact e

/-! ### The reduction -/

variable {U : Set (EuclideanSpace ℝ (Fin d))}

/-- **Localisation step of Evans §6.3.1, Theorem 3.** A local weak solution on `U` of the
equation with coefficients and datum smooth on `U` is, near every compact `K ⊆ U`, a local weak
solution on an open `W ⋐ U` of an equation with the global bounded-measurable coefficients
`localOp` supplies, meeting every mixin `interior_smooth` asks for, and a smooth compactly
supported datum. This is the passage from Evans's classical hypotheses to the `FullEllipticOp`
shape the interior-regularity chain runs on; only the global weak formulation against every
member of `H01 Ω` remains, and it is the sibling interface a later module supplies. -/
theorem localise (P : SmoothOpOn d U) (hU : IsOpen U) {f u : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hsol : LocalWeakSol U P.a P.b P.c f u G)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (Op : FullEllipticOp d) (W : Set (EuclideanSpace ℝ (Fin d)))
      (f' : EuclideanSpace ℝ (Fin d) → ℝ),
      IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ Op.lam = P.lam ∧
      Nonempty (IsC1Coeff Op.toEllipticCoeff) ∧
      (∀ k, Nonempty (IsWkInftyCoeff Op.toEllipticCoeff k)) ∧
      (∀ k, Nonempty (IsWkInftyLower Op k)) ∧
      ContDiff ℝ (⊤ : ℕ∞) f' ∧ HasCompactSupport f' ∧ (∀ x ∈ W, f' x = f x) ∧
      LocalWeakSol W Op.a Op.b Op.c f' u G := by
  obtain ⟨χ, hχ, hχ01, W, hWo, hKW, hWc, hWU, hW1, hlam, ha, hb, hc, h1, hk, hl⟩ :=
    exists_localOp P hU hK hKU
  have hWU' : W ⊆ U := subset_closure.trans hWU
  obtain ⟨hf's, hf'c⟩ := datum_cutoff hU hχ hf
  have hf'W : ∀ x ∈ W, χ x * f x = f x := fun x hx => by simp [hW1 x hx]
  refine ⟨localOp P hU hχ hχ01, W, fun x => χ x * f x, hWo, hKW, hWc, hWU, hlam, h1, hk, hl,
    hf's, hf'c, hf'W, ?_⟩
  exact (hsol.mono hWU').congr hWo.measurableSet (fun x hx => (ha x hx).symm)
    (fun x hx => (hb x hx).symm) (fun x hx => (hc x hx).symm) (fun x hx => (hf'W x hx).symm)

end EllipticPdes.Regularity
