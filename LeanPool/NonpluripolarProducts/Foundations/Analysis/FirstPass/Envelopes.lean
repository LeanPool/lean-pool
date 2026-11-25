/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Actual extended-real upper envelopes

The Lean constructions use the supremum and upper regularization in
[Xia's definition of the prescribed-singularity envelope](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_envelopes.tex#L91-L99).
`thetaPshSupremum` is the pointwise supremum of normalized theta-PSH
potentials. `singularityEnvelope` takes the upper semicontinuous
regularization of the supremum over those more singular than the reference
function. A single real additive constant compares each competitor with
the reference function. An empty competitor set gives the constant bottom
function.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

section Regularization

variable {X : Type*} [TopologicalSpace X]

/-- The upper semicontinuous regularization, as the infimum of the local
suprema over all neighborhoods. Neither infinity is converted to a real. -/
def uscRegularization (f : X → EReal) (x : X) : EReal :=
  ⨅ U ∈ 𝓝 x, ⨆ y ∈ U, f y

theorem le_uscRegularization (f : X → EReal) : f ≤ uscRegularization f := by
  intro x
  apply le_iInf
  intro U
  apply le_iInf
  intro hU
  exact le_iSup_of_le x (le_iSup_of_le (mem_of_mem_nhds hU) le_rfl)

theorem uscRegularization_le_localSup (f : X → EReal) {x : X} {U : Set X}
    (hU : U ∈ 𝓝 x) : uscRegularization f x ≤ ⨆ y ∈ U, f y :=
  iInf_le_of_le U (iInf_le_of_le hU le_rfl)

theorem uscRegularization_mono {f g : X → EReal} (hfg : f ≤ g) :
    uscRegularization f ≤ uscRegularization g := by
  intro x
  exact iInf_mono fun U => iInf_mono fun _ => iSup_mono fun y => iSup_mono fun _ => hfg y

theorem upperSemicontinuous_uscRegularization (f : X → EReal) :
    UpperSemicontinuous (uscRegularization f) := by
  intro x a ha
  obtain ⟨U, hU⟩ := iInf_lt_iff.mp ha
  obtain ⟨hUx, hUa⟩ := iInf_lt_iff.mp hU
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hUx
  filter_upwards [hW.mem_nhds hxW] with y hy
  exact (uscRegularization_le_localSup f
    (mem_of_superset (hW.mem_nhds hy) hWU)).trans_lt hUa

/-- The regularization lies below every upper semicontinuous majorant. -/
theorem uscRegularization_le {f g : X → EReal} (hg : UpperSemicontinuous g)
    (hfg : f ≤ g) : uscRegularization f ≤ g := by
  intro x
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b, hxb, hba⟩ := exists_between ha
  have hU : {y | g y < b} ∈ 𝓝 x := hg x b hxb
  exact ((uscRegularization_le_localSup f hU).trans
    (iSup_le fun y => iSup_le fun hy => (hfg y).trans (le_of_lt hy))).trans_lt hba

theorem uscRegularization_le_iff {f g : X → EReal} (hg : UpperSemicontinuous g) :
    uscRegularization f ≤ g ↔ f ≤ g :=
  ⟨fun h => (le_uscRegularization f).trans h, uscRegularization_le hg⟩

theorem uscRegularization_eq {f : X → EReal} (hf : UpperSemicontinuous f) :
    uscRegularization f = f :=
  le_antisymm (uscRegularization_le hf le_rfl) (le_uscRegularization f)

@[simp] theorem uscRegularization_idem (f : X → EReal) :
    uscRegularization (uscRegularization f) = uscRegularization f :=
  uscRegularization_eq (upperSemicontinuous_uscRegularization f)

/-- This includes both the constant positive- and negative-infinite functions. -/
@[simp] theorem uscRegularization_const (c : EReal) :
    uscRegularization (fun _ : X => c) = fun _ => c :=
  uscRegularization_eq upperSemicontinuous_const

/-- Adding a finite constant preserves upper semicontinuity for
extended-real-valued functions.  Addition on `EReal` is not continuous at
the two indeterminate pairs, but a finite second summand excludes both. -/
theorem upperSemicontinuous_add_coe_const {f : X → EReal}
    (hf : UpperSemicontinuous f) (c : ℝ) :
    UpperSemicontinuous (fun x => f x + (c : EReal)) :=
  hf.add' upperSemicontinuous_const fun _ =>
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot c))
      (Or.inr (EReal.coe_ne_top c))

/-- Upper-semicontinuous regularization commutes with translation by a
finite constant. -/
theorem uscRegularization_add_coe_const (f : X → EReal) (c : ℝ) :
    uscRegularization (fun x => f x + (c : EReal)) =
      fun x => uscRegularization f x + (c : EReal) := by
  have hnegpos : (-(c : EReal) + (c : EReal)) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  have hposneg : ((c : EReal) + -(c : EReal)) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  apply le_antisymm
  · exact uscRegularization_le
      (upperSemicontinuous_add_coe_const
        (upperSemicontinuous_uscRegularization f) c)
      (fun x => by gcongr; exact le_uscRegularization f x)
  · have h : uscRegularization f ≤ fun x =>
        uscRegularization (fun y => f y + (c : EReal)) x + ((-c : ℝ) : EReal) := by
      apply uscRegularization_le
        (upperSemicontinuous_add_coe_const
          (upperSemicontinuous_uscRegularization
            (fun y => f y + (c : EReal))) (-c))
      intro x
      rw [← (EReal.addLECancellable_coe c).add_le_add_iff_right]
      simpa [add_assoc, hnegpos] using
        (le_uscRegularization (fun y => f y + (c : EReal)) x)
    intro x
    rw [← (EReal.addLECancellable_coe (-c)).add_le_add_iff_right]
    simpa [add_assoc, hposneg] using h x

/-- Regularizing a pointwise supremum gives the least USC common majorant. -/
theorem uscRegularization_sSup_le_iff {F : Set (X → EReal)} {g : X → EReal}
    (hg : UpperSemicontinuous g) :
    uscRegularization (sSup F) ≤ g ↔ ∀ f ∈ F, f ≤ g := by
  rw [uscRegularization_le_iff hg, sSup_le_iff]

end Regularization

section Envelopes

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual normalized, locally nondegenerate theta-PSH competitors. -/
def thetaPshCompetitors (θ : SmoothRealForm n M 2) : Set (M → EReal) :=
  {u | IsThetaPshPotential θ u ∧ u ≤ 0}

/-- The pointwise supremum V_theta from the revised source. No regularity
or nonemptiness is built into this definition. -/
def thetaPshSupremum (θ : SmoothRealForm n M 2) : M → EReal :=
  sSup (thetaPshCompetitors θ)

/-- The competitors in P_theta[phi]; the additive comparison is global and
has precisely the manuscript's direction, competitor ≤ phi + C. -/
def singularityCompetitors (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    Set (M → EReal) :=
  {u | u ∈ thetaPshCompetitors θ ∧ MoreSingularOn u φ univ}

/-- The raw supremum before upper semicontinuous regularization. -/
def singularitySupremum (θ : SmoothRealForm n M 2) (φ : M → EReal) : M → EReal :=
  sSup (singularityCompetitors θ φ)

/-- The actual singularity-type envelope P_theta[phi]. It is defined even
when no competitors exist, in which case it is identically negative infinity. -/
def singularityEnvelope (θ : SmoothRealForm n M 2) (φ : M → EReal) : M → EReal :=
  uscRegularization (singularitySupremum θ φ)

theorem thetaPshSupremum_apply (θ : SmoothRealForm n M 2) (x : M) :
    thetaPshSupremum θ x = ⨆ u ∈ thetaPshCompetitors θ, u x := by
  simp only [thetaPshSupremum, sSup_apply, iSup_subtype]

theorem le_thetaPshSupremum {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (hu0 : u ≤ 0) : u ≤ thetaPshSupremum θ :=
  le_sSup ⟨hu, hu0⟩

theorem thetaPshSupremum_le_iff {θ : SmoothRealForm n M 2} {g : M → EReal} :
    thetaPshSupremum θ ≤ g ↔ ∀ u, IsThetaPshPotential θ u → u ≤ 0 → u ≤ g := by
  simp only [thetaPshSupremum, sSup_le_iff, thetaPshCompetitors, mem_ofPred_eq, and_imp]

theorem thetaPshSupremum_le_zero (θ : SmoothRealForm n M 2) :
    thetaPshSupremum θ ≤ 0 :=
  sSup_le fun _ hu => hu.2

theorem singularitySupremum_le_thetaPshSupremum (θ : SmoothRealForm n M 2)
    (φ : M → EReal) : singularitySupremum θ φ ≤ thetaPshSupremum θ :=
  sSup_le_sSup fun _ hu => hu.1

theorem singularitySupremum_le_envelope (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    singularitySupremum θ φ ≤ singularityEnvelope θ φ :=
  le_uscRegularization _

theorem le_singularityEnvelope {θ : SmoothRealForm n M 2} {φ u : M → EReal}
    (hu : IsThetaPshPotential θ u) (hu0 : u ≤ 0) (huφ : MoreSingularOn u φ univ) :
    u ≤ singularityEnvelope θ φ :=
  (le_sSup (s := singularityCompetitors θ φ) ⟨⟨hu, hu0⟩, huφ⟩).trans
    (singularitySupremum_le_envelope θ φ)

theorem self_le_singularityEnvelope {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) (hφ0 : φ ≤ 0) : φ ≤ singularityEnvelope θ φ :=
  le_singularityEnvelope hφ hφ0 (.refl φ univ)

theorem upperSemicontinuous_singularityEnvelope (θ : SmoothRealForm n M 2)
    (φ : M → EReal) : UpperSemicontinuous (singularityEnvelope θ φ) :=
  upperSemicontinuous_uscRegularization _

/-- Universal property among USC majorants, not a claim that P has the same
singularity type as phi. That stronger claim is generally false. -/
theorem singularityEnvelope_le_iff {θ : SmoothRealForm n M 2} {φ g : M → EReal}
    (hg : UpperSemicontinuous g) :
    singularityEnvelope θ φ ≤ g ↔
      ∀ u, IsThetaPshPotential θ u → u ≤ 0 → MoreSingularOn u φ univ → u ≤ g := by
  simpa only [singularityEnvelope, singularitySupremum, singularityCompetitors,
    thetaPshCompetitors, mem_ofPred_eq, and_imp] using
    (uscRegularization_sSup_le_iff (F := singularityCompetitors θ φ) hg)

theorem singularityEnvelope_le_zero (θ : SmoothRealForm n M 2) (φ : M → EReal) :
    singularityEnvelope θ φ ≤ 0 :=
  (singularityEnvelope_le_iff upperSemicontinuous_const).mpr fun _ _ hu0 _ => hu0

theorem thetaPshSupremum_ne_top (θ : SmoothRealForm n M 2) (x : M) :
    thetaPshSupremum θ x ≠ ⊤ :=
  ne_of_lt ((thetaPshSupremum_le_zero θ x).trans_lt (by simp))

theorem singularityEnvelope_ne_top (θ : SmoothRealForm n M 2) (φ : M → EReal) (x : M) :
    singularityEnvelope θ φ x ≠ ⊤ :=
  ne_of_lt ((singularityEnvelope_le_zero θ φ x).trans_lt (by simp))

theorem thetaPshSupremum_of_empty {θ : SmoothRealForm n M 2}
    (h : thetaPshCompetitors θ = ∅) : thetaPshSupremum θ = ⊥ := by
  simp [thetaPshSupremum, h]

theorem singularityEnvelope_of_empty {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (h : singularityCompetitors θ φ = ∅) : singularityEnvelope θ φ = ⊥ := by
  unfold singularityEnvelope singularitySupremum
  rw [h, sSup_empty]
  exact uscRegularization_const ⊥

theorem singularityCompetitors_mono {θ : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (hφψ : MoreSingularOn φ ψ univ) :
    singularityCompetitors θ φ ⊆ singularityCompetitors θ ψ :=
  fun _ hu => ⟨hu.1, hu.2.trans hφψ⟩

theorem singularityEnvelope_mono {θ : SmoothRealForm n M 2} {φ ψ : M → EReal}
    (hφψ : MoreSingularOn φ ψ univ) : singularityEnvelope θ φ ≤ singularityEnvelope θ ψ :=
  uscRegularization_mono (sSup_le_sSup (singularityCompetitors_mono hφψ))

theorem singularityEnvelope_eq_of_sameSingularityType {θ : SmoothRealForm n M 2}
    {φ ψ : M → EReal} (hφψ : SameSingularityTypeOn φ ψ univ) :
    singularityEnvelope θ φ = singularityEnvelope θ ψ :=
  le_antisymm (singularityEnvelope_mono hφψ.1) (singularityEnvelope_mono hφψ.2)

theorem singularityEnvelope_add_const (θ : SmoothRealForm n M 2) (φ : M → EReal) (c : ℝ) :
    singularityEnvelope θ (fun x => φ x + (c : EReal)) = singularityEnvelope θ φ :=
  singularityEnvelope_eq_of_sameSingularityType (sameSingularityTypeOn_add_const φ univ c)

theorem thetaPshCompetitors_geometricallyEq {θ η : SmoothRealForm n M 2}
    (hθη : θ.GeometricallyEq η) : thetaPshCompetitors θ = thetaPshCompetitors η := by
  ext u
  exact and_congr (hθη.thetaPshPotential_iff u) Iff.rfl

theorem thetaPshSupremum_geometricallyEq {θ η : SmoothRealForm n M 2}
    (hθη : θ.GeometricallyEq η) : thetaPshSupremum θ = thetaPshSupremum η := by
  unfold thetaPshSupremum
  rw [thetaPshCompetitors_geometricallyEq hθη]

theorem singularityEnvelope_geometricallyEq {θ η : SmoothRealForm n M 2}
    (hθη : θ.GeometricallyEq η) (φ : M → EReal) :
    singularityEnvelope θ φ = singularityEnvelope η φ := by
  unfold singularityEnvelope singularitySupremum singularityCompetitors
  rw [thetaPshCompetitors_geometricallyEq hθη]

/-- A larger function retains local nondegeneracy, including at pole values. -/
theorem LocallyNondegenerate.mono {u v : M → EReal} (hu : LocallyNondegenerate u)
    (huv : u ≤ v) : LocallyNondegenerate v := by
  intro x U hU hx
  obtain ⟨y, hy, hfin⟩ := hu x U hU hx
  exact ⟨y, hy, ne_bot_of_le_ne_bot hfin (huv y)⟩

theorem thetaPshSupremum_locallyNondegenerate {θ : SmoothRealForm n M 2}
    (hne : (thetaPshCompetitors θ).Nonempty) : LocallyNondegenerate (thetaPshSupremum θ) := by
  obtain ⟨u, hu, hu0⟩ := hne
  exact hu.2.mono (le_thetaPshSupremum hu hu0)

theorem singularityEnvelope_locallyNondegenerate {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hne : (singularityCompetitors θ φ).Nonempty) :
    LocallyNondegenerate (singularityEnvelope θ φ) := by
  obtain ⟨u, ⟨hu, hu0⟩, huφ⟩ := hne
  exact hu.2.mono (le_singularityEnvelope hu hu0 huφ)

end Envelopes

end

end SGPT.Foundations.Analysis.FirstPass
