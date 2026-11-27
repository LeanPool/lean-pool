/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The unit cube as a fundamental domain of `ℤ^m`

Two facts about `ℤ^m`-periodic functions on `ℝ^m = Fin m → ℝ` and the open unit cube
`(0, 1)^m = unitCube m`, which is, up to a null set, a fundamental domain of `ℤ^m`:

* `setIntegral_unitCube_comp_add`: translation invariance, `∫_{(0,1)^m} f (x + a) dx =
  ∫_{(0,1)^m} f (x) dx` for a periodic `f`;
* `ae_of_ae_restrict_unitCube_of_periodic`: a property that holds almost everywhere on `(0, 1)^m`
  and passes from `x + k` to `x` for every `k ∈ ℤ^m` (in particular, a `ℤ^m`-periodic property)
  holds almost everywhere on `ℝ^m`.

Translation invariance comes from Mathlib's fundamental domains: `[0, 1)^m` is a fundamental domain
of the lattice `ℤ^m` (`ZSpan.isAddFundamentalDomain`), so is its translate by `a`, and two
fundamental domains carry the same integral of a `ℤ^m`-invariant function
(`IsAddFundamentalDomain.setIntegral_eq`); `(0, 1)^m` differs from `[0, 1)^m` by a null set. These
facts are standard.
-/

@[expose] public section

open MeasureTheory Filter

namespace CalculusOfVariations

open scoped Pointwise

variable {m : ℕ}

/-- Translation invariance of the integral over the unit cube: for a `ℤ^m`-periodic `f`,
`∫_{(0,1)^m} f (x + a) dx = ∫_{(0,1)^m} f (x) dx`. No integrability is needed: two fundamental
domains carry the same integral of every `ℤ^m`-invariant function
(`IsAddFundamentalDomain.setIntegral_eq`). -/
theorem setIntegral_unitCube_comp_add {f : (Fin m → ℝ) → ℝ}
    (hf : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), f (x + fun i => (z i : ℝ)) = f x) (a : Fin m → ℝ) :
    ∫ x in unitCube m, f (x + a) = ∫ x in unitCube m, f x := by
  set b := Pi.basisFun ℝ (Fin m)
  set F : Set (Fin m → ℝ) := Set.pi Set.univ fun _ => Set.Ico (0:ℝ) 1
  -- `[0, 1)^m` is a fundamental domain of `ℤ^m = span_ℤ (standard basis)`
  have hFD : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)) F volume := by
    have := ZSpan.isAddFundamentalDomain b volume
    rwa [ZSpan.fundamentalDomain_pi_basisFun] at this
  have hQF : (unitCube m : Set (Fin m → ℝ)) =ᵐ[volume] F := by
    have h1 := Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := fun _ => (0:ℝ)) (g := fun _ => 1)
    have h2 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := fun _ => (0:ℝ)) (g := fun _ => 1)
    exact h1.trans h2.symm
  -- `f` is invariant under the lattice
  have hinv : ∀ (g : Submodule.span ℤ (Set.range b)) (x : Fin m → ℝ), f (g +ᵥ x) = f x := by
    intro g x
    have hg := (Module.Basis.mem_span_iff_repr_mem ℤ b (g : Fin m → ℝ)).1 g.2
    choose z hz using fun i => hg i
    have : (g : Fin m → ℝ) = fun i => (z i : ℝ) := by
      funext i
      have := hz i
      simp only [b, Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at this
      exact this.symm
    rw [Submodule.vadd_def, vadd_eq_add, this, add_comm]
    exact hf x z
  have : VAddInvariantMeasure (Submodule.span ℤ (Set.range b)) (Fin m → ℝ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin m → ℝ) s⟩
  -- the translate `a + [0, 1)^m` is a fundamental domain too
  have hFD' : IsAddFundamentalDomain (Submodule.span ℤ (Set.range b)) (a +ᵥ F) volume :=
    hFD.vadd_of_comm a
  have h := (measurePreserving_add_right (volume : Measure (Fin m → ℝ)) a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) f (a +ᵥ F)
  have hpre : (fun x => x + a) ⁻¹' (a +ᵥ F) = F := by
    ext x
    simp [Set.mem_vadd_set, add_comm]
  rw [hpre] at h
  rw [setIntegral_congr_set hQF, setIntegral_congr_set hQF, h]
  exact hFD'.setIntegral_eq hFD hinv

/-- A property that holds almost everywhere on the unit cube `(0, 1)^m` and passes from `x + k` to
`x` for every `k ∈ ℤ^m` holds almost everywhere on `ℝ^m`: every `x` has a translate `x − ⌊x⌋` in
`[0, 1)^m`, which differs from the open cube by a null set, and the translations by `ℤ^m` preserve
the Lebesgue measure. -/
theorem ae_of_ae_restrict_unitCube_of_periodic {P : (Fin m → ℝ) → Prop}
    (hP : ∀ (x : Fin m → ℝ) (k : Fin m → ℤ), P (x + fun i => (k i : ℝ)) → P x)
    (h : ∀ᵐ x ∂(volume.restrict (unitCube m)), P x) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), P x := by
  have hIco : (unitCube m : Set (Fin m → ℝ))
      =ᵐ[(volume : Measure (Fin m → ℝ))] (Set.pi Set.univ fun _ : Fin m => Set.Ico (0 : ℝ) 1) :=
    (Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => 1)).trans
      (Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
      (f := fun _ => (0 : ℝ)) (g := fun _ => 1)).symm
  rw [Measure.restrict_congr_set hIco,
    ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ico)] at h
  have hk : ∀ k : Fin m → ℤ, ∀ᵐ x : Fin m → ℝ,
      (x + fun i => (k i : ℝ)) ∈ (Set.pi Set.univ fun _ : Fin m => Set.Ico (0 : ℝ) 1) →
        P (x + fun i => (k i : ℝ)) := fun k =>
    (measurePreserving_add_right volume (fun i => (k i : ℝ))).quasiMeasurePreserving.ae h
  filter_upwards [ae_all_iff.2 hk] with x hx
  refine hP x (fun i => -⌊x i⌋) (hx _ fun i _ => ?_)
  simp only [Int.cast_neg, Set.mem_Ico, Pi.add_apply]
  constructor <;> linarith [Int.floor_le (x i), Int.lt_floor_add_one (x i)]

end CalculusOfVariations
