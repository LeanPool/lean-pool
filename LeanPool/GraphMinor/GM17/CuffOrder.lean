/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Finset.Sort

/-!
# Circular Order on Cuffs and Cuff Enumerations in Paintings

This file proves the properties of circular order `GM19.InOrderOn` on a cuff $\Theta$ (cyclic
shifts, reversal, and index orderings) and constructs the canonical cyclic enumeration
`Painting.CuffEnumeration` of the nodes and border cells around any cuff $\Theta$ of a painting
$\Gamma$ in a surface $S$.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM19

universe u

/-! ## 1. Properties of `GM19.cuffPoint` and `GM19.InOrderOn` -/

section CuffPoint

variable {S : Type u} [TopologicalSpace S] {Θ : Set S}

theorem cuffPoint_mem (f : Circle ≃ₜ Θ) (t : ℝ) : cuffPoint f t ∈ Θ :=
  (f (Circle.exp t)).2

theorem cuffPoint_continuous (f : Circle ≃ₜ Θ) : Continuous (cuffPoint f) :=
  continuous_subtype_val.comp (f.continuous.comp Circle.exp.continuous)

theorem cuffPoint_eq_iff (f : Circle ≃ₜ Θ) {t₁ t₂ : ℝ} :
    cuffPoint f t₁ = cuffPoint f t₂ ↔ ∃ m : ℤ, t₁ = t₂ + m * (2 * Real.pi) := by
  simp only [cuffPoint]
  constructor
  · intro h
    have h1 : f (Circle.exp t₁) = f (Circle.exp t₂) := Subtype.ext h
    have h2 : Circle.exp t₁ = Circle.exp t₂ := f.injective h1
    rw [Circle.exp_eq_exp] at h2
    exact h2
  · rintro ⟨m, rfl⟩
    have h2 : Circle.exp (t₂ + m * (2 * Real.pi)) = Circle.exp t₂ :=
      Circle.exp_eq_exp.mpr ⟨m, rfl⟩
    rw [h2]

theorem cuffPoint_add_two_pi (f : Circle ≃ₜ Θ) (t : ℝ) :
    cuffPoint f (t + 2 * Real.pi) = cuffPoint f t :=
  (cuffPoint_eq_iff f).mpr ⟨1, by push_cast; ring⟩

theorem cuffPoint_sub_two_pi (f : Circle ≃ₜ Θ) (t : ℝ) :
    cuffPoint f (t - 2 * Real.pi) = cuffPoint f t :=
  (cuffPoint_eq_iff f).mpr ⟨-1, by push_cast; ring⟩

theorem cuffPoint_injOn_Ico (f : Circle ≃ₜ Θ) (t₀ : ℝ) :
    InjOn (cuffPoint f) (Ico t₀ (t₀ + 2 * Real.pi)) := by
  intro t₁ ht₁ t₂ ht₂ h
  obtain ⟨m, rfl⟩ := (cuffPoint_eq_iff f).mp h
  have hpi : 0 < 2 * Real.pi := by positivity
  have hm0 : m = 0 := by
    by_contra hm
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have hm_le : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      have : (m : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hm_le hpi.le
      linarith [ht₁.1, ht₂.2]
    · have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hgt
      have : 1 * (2 * Real.pi) ≤ (m : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hm_ge hpi.le
      linarith [ht₁.2, ht₂.1]
  simp [hm0]

theorem exists_cuffPoint_mem_Ico (f : Circle ≃ₜ Θ) (t₀ : ℝ) {x : S} (hx : x ∈ Θ) :
    ∃ t ∈ Ico t₀ (t₀ + 2 * Real.pi), cuffPoint f t = x := by
  let z : Circle := f.symm ⟨x, hx⟩
  have hz : (f z).1 = x := congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)
  let θ₀ : ℝ := Complex.arg (z : ℂ)
  have hexp₀ : Circle.exp θ₀ = z := Circle.exp_arg z
  have hpi : 0 < 2 * Real.pi := by positivity
  let m : ℤ := ⌊(θ₀ - t₀) / (2 * Real.pi)⌋
  let t : ℝ := θ₀ - m * (2 * Real.pi)
  have hm_le : (m : ℝ) ≤ (θ₀ - t₀) / (2 * Real.pi) := Int.floor_le _
  have hm_lt : (θ₀ - t₀) / (2 * Real.pi) < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have h1 : (m : ℝ) * (2 * Real.pi) ≤ θ₀ - t₀ := (le_div_iff₀ hpi).mp hm_le
  have h2 : θ₀ - t₀ < ((m : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ hpi).mp hm_lt
  refine ⟨t, ⟨by linarith, by linarith⟩, ?_⟩
  have h_eq : cuffPoint f t = cuffPoint f θ₀ :=
    (cuffPoint_eq_iff f).mpr ⟨-m, by push_cast; ring⟩
  rw [h_eq, cuffPoint, hexp₀, hz]

/-- Every `O`-arc is infinite. -/
theorem infinite_of_isOArc (hΘ : IsOArc Θ) : Θ.Infinite := by
  rcases hΘ with ⟨f⟩
  have hlt : (0 : ℝ) < 0 + 2 * Real.pi := by positivity
  have hinf : (Ico (0 : ℝ) (0 + 2 * Real.pi)).Infinite := Set.Ico_infinite hlt
  refine (hinf.image (cuffPoint_injOn_Ico f 0)).mono ?_
  rintro _ ⟨t, _, rfl⟩
  exact cuffPoint_mem f t

/-! ### Symmetries of `GM19.InOrderOn` -/

/-- Cyclic permutation of `GM19.InOrderOn`: if $n_1, n_2, n_3, n_4$ are in order on $\Theta$,
then $n_2, n_3, n_4, n_1$ are in order on $\Theta$. -/
theorem inOrderOn_cyclic {n₁ n₂ n₃ n₄ : S} (h : InOrderOn Θ n₁ n₂ n₃ n₄) :
    InOrderOn Θ n₂ n₃ n₄ n₁ := by
  rcases h with ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, hn₁, hn₂, hn₃, hn₄⟩
  refine ⟨f, t₂, t₃, t₄, t₁ + 2 * Real.pi, h23, h34, h41, by linarith,
    hn₂, hn₃, hn₄, ?_⟩
  rw [cuffPoint_add_two_pi, hn₁]

theorem inOrderOn_cyclic2 {n₁ n₂ n₃ n₄ : S} (h : InOrderOn Θ n₁ n₂ n₃ n₄) :
    InOrderOn Θ n₃ n₄ n₁ n₂ :=
  inOrderOn_cyclic (inOrderOn_cyclic h)

theorem inOrderOn_cyclic3 {n₁ n₂ n₃ n₄ : S} (h : InOrderOn Θ n₁ n₂ n₃ n₄) :
    InOrderOn Θ n₄ n₁ n₂ n₃ :=
  inOrderOn_cyclic (inOrderOn_cyclic2 h)

/-- Reversal symmetry of `GM19.InOrderOn`: if $n_1, n_2, n_3, n_4$ are in order on $\Theta$,
then $n_4, n_3, n_2, n_1$ are in order on $\Theta$. -/
theorem inOrderOn_rev {n₁ n₂ n₃ n₄ : S} (h : InOrderOn Θ n₁ n₂ n₃ n₄) :
    InOrderOn Θ n₄ n₃ n₂ n₁ := by
  rcases h with ⟨f, t₁, t₂, t₃, t₄, h12, h23, h34, h41, hn₁, hn₂, hn₃, hn₄⟩
  let f' : Circle ≃ₜ Θ := (Homeomorph.inv Circle).trans f
  have hcp : ∀ t : ℝ, cuffPoint f' (-t) = cuffPoint f t := by
    intro t
    change (f (Circle.exp (-t))⁻¹).1 = (f (Circle.exp t)).1
    rw [Circle.exp_neg, inv_inv]
  refine ⟨f', -t₄, -t₃, -t₂, -t₁, by linarith, by linarith, by linarith, by linarith,
    by rw [hcp, hn₄], by rw [hcp, hn₃], by rw [hcp, hn₂], by rw [hcp, hn₁]⟩

end CuffPoint

/-! ## 2. Cyclic Distance and Cyclic Order in `Fin k` -/

/-- Forward cyclic distance from $i$ to $j$ in `Fin k`: $(j - i) \bmod k$. -/
def cyclicDist {k : ℕ} (i j : Fin k) : ℕ :=
  (j.1 + k - i.1) % k

theorem cyclicDist_eq_ite {k : ℕ} (i j : Fin k) :
    cyclicDist i j = if i.1 ≤ j.1 then j.1 - i.1 else j.1 + k - i.1 := by
  unfold cyclicDist
  have hi := i.2
  have hj := j.2
  split_ifs with h
  · have heq : j.1 + k - i.1 = (j.1 - i.1) + 1 * k := by omega
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem cyclicDist_self {k : ℕ} (i : Fin k) : cyclicDist i i = 0 := by
  rw [cyclicDist_eq_ite]; simp

theorem cyclicDist_pos_of_ne {k : ℕ} {i j : Fin k} (hne : i ≠ j) : 0 < cyclicDist i j := by
  have hval : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
  rw [cyclicDist_eq_ite]
  have hi := i.2
  have hj := j.2
  split_ifs <;> omega

theorem cyclicDist_lt {k : ℕ} (hk : 0 < k) (i j : Fin k) : cyclicDist i j < k :=
  Nat.mod_lt _ hk

/-- If four indices $i_1, i_2, i_3, i_4 \in \text{Fin } k$ satisfy $i_1 \ne i_2$, $i_2 \ne i_3$,
$i_3 \ne i_4$, $i_4 \ne i_1$ and
$\text{cyclicDist } i_1\, i_2 + \text{cyclicDist } i_2\, i_3 + \text{cyclicDist } i_3\, i_4 \le k$,
then $i_1, i_2, i_3, i_4$ are in strict cyclic order around `Fin k`. -/
theorem cyclicOrder_of_cyclicDist_le {k : ℕ} {i₁ i₂ i₃ i₄ : Fin k}
    (h12 : i₁ ≠ i₂) (h23 : i₂ ≠ i₃) (h34 : i₃ ≠ i₄) (h41 : i₄ ≠ i₁)
    (hle : cyclicDist i₁ i₂ + cyclicDist i₂ i₃ + cyclicDist i₃ i₄ ≤ k) :
    (i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄) ∨
    (i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁) ∨
    (i₃ < i₄ ∧ i₄ < i₁ ∧ i₁ < i₂) ∨
    (i₄ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃) := by
  have v12 : i₁.1 ≠ i₂.1 := fun h => h12 (Fin.ext h)
  have v23 : i₂.1 ≠ i₃.1 := fun h => h23 (Fin.ext h)
  have v34 : i₃.1 ≠ i₄.1 := fun h => h34 (Fin.ext h)
  have v41 : i₄.1 ≠ i₁.1 := fun h => h41 (Fin.ext h)
  have b1 := i₁.2; have b2 := i₂.2; have b3 := i₃.2; have b4 := i₄.2
  rw [cyclicDist_eq_ite, cyclicDist_eq_ite, cyclicDist_eq_ite] at hle
  simp only [Fin.lt_def]
  split_ifs at hle <;> omega

/-- In any `CuffEnumeration`, four indices in strict cyclic order around `Fin k` have their
nodes in circular order on $\Theta$. -/
theorem Painting.CuffEnumeration.inOrderOn_of_cyclic {S : Type} [TopologicalSpace S]
    {Γ : Painting S} {Θ : Set S} {k : ℕ} (E : Γ.CuffEnumeration Θ k)
    {i₁ i₂ i₃ i₄ : Fin k}
    (h : (i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄) ∨
         (i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < i₁) ∨
         (i₃ < i₄ ∧ i₄ < i₁ ∧ i₁ < i₂) ∨
         (i₄ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃)) :
    InOrderOn Θ (E.node i₁) (E.node i₂) (E.node i₃) (E.node i₄) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact E.nodes_in_order i₁ i₂ i₃ i₄ h1 h2 h3
  · exact inOrderOn_cyclic3 (E.nodes_in_order i₂ i₃ i₄ i₁ h1 h2 h3)
  · exact inOrderOn_cyclic2 (E.nodes_in_order i₃ i₄ i₁ i₂ h1 h2 h3)
  · exact inOrderOn_cyclic (E.nodes_in_order i₄ i₁ i₂ i₃ h1 h2 h3)

/-- In any portrayal $\pi$ and cuff enumeration $E$ of $\Theta$, if four indices
$i_1, i_2, i_3, i_4 \in \text{Fin } k$ satisfy
$\text{cyclicDist } i_1\, i_2 + \text{cyclicDist } i_2\, i_3 + \text{cyclicDist } i_3\, i_4 \le k$,
then $\beta(n_{i_1} +) \cap \beta(n_{i_3} +) \subseteq \beta(n_{i_2} +) \cup \beta(n_{i_4} +)$
(whether or not the four indices are distinct). -/
theorem Portrayal.p7_of_cyclicDist {α : Type*} {β : Type*} {G : Hypergraph α β}
    (π : Portrayal G) {Θ : Set π.S} {k : ℕ} (E : π.Γ.CuffEnumeration Θ k)
    {i₁ i₂ i₃ i₄ : Fin k}
    (hle : cyclicDist i₁ i₂ + cyclicDist i₂ i₃ + cyclicDist i₃ i₄ ≤ k)
    {v : α} (hv₁ : v ∈ π.borderPlus (E.node i₁)) (hv₃ : v ∈ π.borderPlus (E.node i₃)) :
    v ∈ π.borderPlus (E.node i₂) ∨ v ∈ π.borderPlus (E.node i₄) := by
  by_cases h12 : i₁ = i₂
  · exact Or.inl (h12 ▸ hv₁)
  by_cases h23 : i₂ = i₃
  · exact Or.inl (h23.symm ▸ hv₃)
  by_cases h34 : i₃ = i₄
  · exact Or.inr (h34 ▸ hv₃)
  by_cases h41 : i₄ = i₁
  · exact Or.inr (h41.symm ▸ hv₁)
  have hord := E.inOrderOn_of_cyclic (cyclicOrder_of_cyclicDist_le h12 h23 h34 h41 hle)
  have hn_mem : ∀ i : Fin k, E.node i ∈ π.Γ.N ∩ Θ := by
    intro i
    rw [← E.range_node]
    exact mem_range_self i
  exact π.p7 Θ E.cuff_mem (E.node i₁) (hn_mem i₁) (E.node i₂) (hn_mem i₂)
    (E.node i₃) (hn_mem i₃) (E.node i₄) (hn_mem i₄) hord v hv₁ hv₃

/-! ## 3. Construction of `Painting.CuffEnumeration` -/

section CuffEnumeration

variable {S : Type} [TopologicalSpace S] (Γ : Painting S) {Θ : Set S}

private noncomputable def angleOf (f : Circle ≃ₜ Θ) (x : S) : ℝ := by
  classical
  exact if hx : x ∈ Θ then Classical.choose (exists_cuffPoint_mem_Ico f 0 hx) else 0

private theorem angleOf_mem_Ico (f : Circle ≃ₜ Θ) {x : S} (hx : x ∈ Θ) :
    angleOf f x ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) := by
  simp only [angleOf, hx, dite_true]
  exact (Classical.choose_spec (exists_cuffPoint_mem_Ico f 0 hx)).1

private theorem cuffPoint_angleOf (f : Circle ≃ₜ Θ) {x : S} (hx : x ∈ Θ) :
    cuffPoint f (angleOf f x) = x := by
  simp only [angleOf, hx, dite_true]
  exact (Classical.choose_spec (exists_cuffPoint_mem_Ico f 0 hx)).2

private theorem angleOf_cuffPoint (f : Circle ≃ₜ Θ) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi)) :
    angleOf f (cuffPoint f t) = t := by
  have hx : cuffPoint f t ∈ Θ := cuffPoint_mem f t
  exact cuffPoint_injOn_Ico f 0 (angleOf_mem_Ico f hx) ht (cuffPoint_angleOf f hx)

private theorem angleOf_injOn (f : Circle ≃ₜ Θ) : InjOn (angleOf f) Θ := by
  intro x hx y hy h
  rw [← cuffPoint_angleOf f hx, ← cuffPoint_angleOf f hy, h]

/-- Every cuff $\Theta$ of a surface $S$ contains at least two nodes of any painting $\Gamma$. -/
theorem Painting.two_le_ncard_nodes_inter_cuff (hΘ : Θ ∈ cuffs S) (hΘ_arc : IsOArc Θ) :
    2 ≤ (Γ.N ∩ Θ).ncard := by
  have hinf : Θ.Infinite := infinite_of_isOArc hΘ_arc
  have hinf_diff : (Θ \ Γ.N).Infinite := hinf.sdiff Γ.finite_N
  obtain ⟨x, hxΘ, hxN⟩ := hinf_diff.nonempty
  rcases hΘ with ⟨x₀, hx₀, hΘ_eq⟩
  have hx_comp : x ∈ connectedComponentIn (bd S) x₀ := by rwa [hΘ_eq]
  have hxbd : x ∈ bd S := connectedComponentIn_subset (bd S) x₀ hx_comp
  obtain ⟨c, ⟨hc, hxc⟩, _⟩ := Γ.exists_border_cell_of_mem_bd ⟨hxbd, hxN⟩
  have hΘ' : Θ ∈ cuffs S := ⟨x₀, hx₀, hΘ_eq⟩
  have hinter : (c ∩ Θ).Nonempty := ⟨x, hxc, hxΘ⟩
  have htilde_sub : tilde c ⊆ Γ.N ∩ Θ := (Γ.border_cell_subset_cuff hc hΘ' hinter).2.2.2.1
  have hncard : (tilde c).ncard = 2 := (Γ.border_cell c hc ⟨x, hxc, hxbd⟩).1
  have hfin : (Γ.N ∩ Θ).Finite := Γ.finite_N.inter_of_left Θ
  linarith [ncard_le_ncard htilde_sub hfin]

private noncomputable def nodeAngleFinset (f : Circle ≃ₜ Θ) : Finset ℝ :=
  ((Γ.finite_N.inter_of_left Θ).toFinset).image (angleOf f)

private theorem card_nodeAngleFinset (f : Circle ≃ₜ Θ) :
    (nodeAngleFinset Γ f).card = (Γ.N ∩ Θ).ncard := by
  unfold nodeAngleFinset
  have hinj : InjOn (angleOf f) ((Γ.finite_N.inter_of_left Θ).toFinset : Set S) := by
    refine (angleOf_injOn f).mono ?_
    rw [Set.Finite.coe_toFinset]
    exact inter_subset_right
  rw [Finset.card_image_of_injOn hinj, ← ncard_eq_toFinset_card (Γ.N ∩ Θ)
    (Γ.finite_N.inter_of_left Θ)]

private noncomputable def nodeAngle (f : Circle ≃ₜ Θ) (i : Fin (Γ.N ∩ Θ).ncard) : ℝ :=
  (nodeAngleFinset Γ f).orderEmbOfFin (card_nodeAngleFinset Γ f) i

private theorem strictMono_nodeAngle (f : Circle ≃ₜ Θ) : StrictMono (nodeAngle Γ f) :=
  ((nodeAngleFinset Γ f).orderEmbOfFin (card_nodeAngleFinset Γ f)).strictMono

private theorem range_nodeAngle (f : Circle ≃ₜ Θ) :
    Set.range (nodeAngle Γ f) = angleOf f '' (Γ.N ∩ Θ) := by
  unfold nodeAngle
  rw [Finset.range_orderEmbOfFin, nodeAngleFinset, Finset.coe_image, Set.Finite.coe_toFinset]

private theorem nodeAngle_mem_Ico (f : Circle ≃ₜ Θ) (i : Fin (Γ.N ∩ Θ).ncard) :
    nodeAngle Γ f i ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) := by
  have hmem : nodeAngle Γ f i ∈ Set.range (nodeAngle Γ f) := mem_range_self i
  rw [range_nodeAngle] at hmem
  rcases hmem with ⟨x, ⟨_, hxΘ⟩, h_eq⟩
  rw [← h_eq]
  exact angleOf_mem_Ico f hxΘ

private noncomputable def cuffNode (f : Circle ≃ₜ Θ) (i : Fin (Γ.N ∩ Θ).ncard) : S :=
  cuffPoint f (nodeAngle Γ f i)

private theorem injective_cuffNode (f : Circle ≃ₜ Θ) : Function.Injective (cuffNode Γ f) := by
  intro i j h
  have h_eq : nodeAngle Γ f i = nodeAngle Γ f j :=
    cuffPoint_injOn_Ico f 0 (nodeAngle_mem_Ico Γ f i) (nodeAngle_mem_Ico Γ f j) h
  exact (strictMono_nodeAngle Γ f).injective h_eq

private theorem range_cuffNode (f : Circle ≃ₜ Θ) :
    Set.range (cuffNode Γ f) = Γ.N ∩ Θ := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : nodeAngle Γ f i ∈ Set.range (nodeAngle Γ f) := mem_range_self i
    rw [range_nodeAngle] at hmem
    rcases hmem with ⟨y, hy, hy_eq⟩
    unfold cuffNode
    rw [← hy_eq, cuffPoint_angleOf f hy.2]
    exact hy
  · intro hx
    have hmem : angleOf f x ∈ Set.range (nodeAngle Γ f) := by
      rw [range_nodeAngle]
      exact ⟨x, hx, rfl⟩
    rcases hmem with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    unfold cuffNode
    rw [hi, cuffPoint_angleOf f hx.2]

private theorem cuffNode_inOrderOn (f : Circle ≃ₜ Θ)
    (i₁ i₂ i₃ i₄ : Fin (Γ.N ∩ Θ).ncard) (h12 : i₁ < i₂) (h23 : i₂ < i₃) (h34 : i₃ < i₄) :
    InOrderOn Θ (cuffNode Γ f i₁) (cuffNode Γ f i₂) (cuffNode Γ f i₃) (cuffNode Γ f i₄) := by
  have hmono := strictMono_nodeAngle Γ f
  have ht₁ := (nodeAngle_mem_Ico Γ f i₁).1
  have ht₄ := (nodeAngle_mem_Ico Γ f i₄).2
  exact ⟨f, nodeAngle Γ f i₁, nodeAngle Γ f i₂, nodeAngle Γ f i₃, nodeAngle Γ f i₄,
    (hmono h12).le, (hmono h23).le, (hmono h34).le, by linarith, rfl, rfl, rfl, rfl⟩

private noncomputable def upperAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) : ℝ :=
  if h : i.1 + 1 < (Γ.N ∩ Θ).ncard then
    nodeAngle Γ f ⟨i.1 + 1, h⟩
  else
    nodeAngle Γ f ⟨0, by omega⟩ + 2 * Real.pi

private theorem nodeAngle_lt_upperAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) :
    nodeAngle Γ f i < upperAngle Γ f hk i := by
  unfold upperAngle
  split_ifs with h
  · exact strictMono_nodeAngle Γ f (Nat.lt_succ_self i.1)
  · have hi := (nodeAngle_mem_Ico Γ f i).2
    have h0 := (nodeAngle_mem_Ico Γ f ⟨0, by omega⟩).1
    linarith

private theorem cuffPoint_upperAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffPoint f (upperAngle Γ f hk i) =
      cuffNode Γ f ⟨(i.1 + 1) % (Γ.N ∩ Θ).ncard, Nat.mod_lt _ (by omega)⟩ := by
  unfold upperAngle cuffNode
  split_ifs with h
  · congr 2
    apply Fin.ext
    dsimp
    exact (Nat.mod_eq_of_lt h).symm
  · rw [cuffPoint_add_two_pi]
    congr 2
    apply Fin.ext
    dsimp
    have heq : i.1 + 1 = (Γ.N ∩ Θ).ncard := by have := i.2; omega
    rw [heq, Nat.mod_self]

private theorem notMem_N_of_mem_Ioo (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) {t : ℝ}
    (ht : t ∈ Ioo (nodeAngle Γ f i) (upperAngle Γ f hk i)) :
    cuffPoint f t ∉ Γ.N := by
  intro hxN
  have hx : cuffPoint f t ∈ Γ.N ∩ Θ := ⟨hxN, cuffPoint_mem f t⟩
  rcases ht with ⟨ht₁, ht₂⟩
  unfold upperAngle at ht₂
  split_ifs at ht₂ with h
  · have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
      ⟨(nodeAngle_mem_Ico Γ f i).1.trans ht₁.le,
       ht₂.trans (nodeAngle_mem_Ico Γ f ⟨i.1 + 1, h⟩).2⟩
    have ht_eq : angleOf f (cuffPoint f t) = t := angleOf_cuffPoint f ht_Ico
    have hmem : t ∈ Set.range (nodeAngle Γ f) := by
      rw [range_nodeAngle]
      exact ⟨cuffPoint f t, hx, ht_eq⟩
    rcases hmem with ⟨j, rfl⟩
    have hij : i < j := (strictMono_nodeAngle Γ f).lt_iff_lt.mp ht₁
    have hji : j < ⟨i.1 + 1, h⟩ := (strictMono_nodeAngle Γ f).lt_iff_lt.mp ht₂
    have hij' : i.1 < j.1 := hij
    have hji' : j.1 < i.1 + 1 := hji
    omega
  · by_cases hlt : t < 2 * Real.pi
    · have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨(nodeAngle_mem_Ico Γ f i).1.trans ht₁.le, by linarith⟩
      have ht_eq : angleOf f (cuffPoint f t) = t := angleOf_cuffPoint f ht_Ico
      have hmem : t ∈ Set.range (nodeAngle Γ f) := by
        rw [range_nodeAngle]
        exact ⟨cuffPoint f t, hx, ht_eq⟩
      rcases hmem with ⟨j, rfl⟩
      have hij : i < j := (strictMono_nodeAngle Γ f).lt_iff_lt.mp ht₁
      have hij' : i.1 < j.1 := hij
      have hj_lt := j.2
      omega
    · have ht_Ico : t - 2 * Real.pi ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨by linarith, by linarith [(nodeAngle_mem_Ico Γ f ⟨0, by omega⟩).2]⟩
      have hcp : cuffPoint f (t - 2 * Real.pi) = cuffPoint f t := cuffPoint_sub_two_pi f t
      have ht_eq : angleOf f (cuffPoint f t) = t - 2 * Real.pi := by
        rw [← hcp]
        exact angleOf_cuffPoint f ht_Ico
      have hmem : t - 2 * Real.pi ∈ Set.range (nodeAngle Γ f) := by
        rw [range_nodeAngle]
        exact ⟨cuffPoint f t, hx, ht_eq⟩
      rcases hmem with ⟨j, hj⟩
      have hj0 : nodeAngle Γ f j < nodeAngle Γ f ⟨0, by omega⟩ := by linarith
      have hj_lt : j < ⟨0, by omega⟩ := (strictMono_nodeAngle Γ f).lt_iff_lt.mp hj0
      exact Nat.not_lt_zero j.1 hj_lt

private noncomputable def cuffArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) : Set S :=
  cuffPoint f '' Ioo (nodeAngle Γ f i) (upperAngle Γ f hk i)

private noncomputable def cuffMidAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) : ℝ :=
  (nodeAngle Γ f i + upperAngle Γ f hk i) / 2

private theorem cuffMidAngle_mem_Ioo (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffMidAngle Γ f hk i ∈ Ioo (nodeAngle Γ f i) (upperAngle Γ f hk i) := by
  have hlt := nodeAngle_lt_upperAngle Γ f hk i
  unfold cuffMidAngle
  exact ⟨by linarith, by linarith⟩

private noncomputable def cuffMidpoint (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) : S :=
  cuffPoint f (cuffMidAngle Γ f hk i)

private theorem cuffMidpoint_mem_cuffArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffMidpoint Γ f hk i ∈ cuffArc Γ f hk i :=
  ⟨cuffMidAngle Γ f hk i, cuffMidAngle_mem_Ioo Γ f hk i, rfl⟩

private theorem cuffArc_subset_cuff_diff_N (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffArc Γ f hk i ⊆ Θ \ Γ.N := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨cuffPoint_mem f t, notMem_N_of_mem_Ioo Γ f hk i ht⟩

private theorem cuffArc_subset_U_diff_N (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffArc Γ f hk i ⊆ Γ.U \ Γ.N := by
  rcases hΘ with ⟨x₀, _, rfl⟩
  have hsub : connectedComponentIn (bd S) x₀ ⊆ Γ.U :=
    (connectedComponentIn_subset (bd S) x₀).trans Γ.bd_subset
  exact (cuffArc_subset_cuff_diff_N Γ f hk i).trans (sdiff_subset_sdiff_left hsub)

private theorem isPathConnected_cuffArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) :
    IsPathConnected (cuffArc Γ f hk i) :=
  ((convex_Ioo _ _).isPathConnected ⟨_, cuffMidAngle_mem_Ioo Γ f hk i⟩).image
    (cuffPoint_continuous f)

private theorem angleOf_mem_of_mem_cuffArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) {x : S} (hx : x ∈ cuffArc Γ f hk i) :
    if h : i.1 + 1 < (Γ.N ∩ Θ).ncard then
      nodeAngle Γ f i < angleOf f x ∧ angleOf f x < nodeAngle Γ f ⟨i.1 + 1, h⟩
    else
      nodeAngle Γ f i < angleOf f x ∨ angleOf f x < nodeAngle Γ f ⟨0, by omega⟩ := by
  rcases hx with ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
  have hxN : cuffPoint f t ∉ Γ.N := notMem_N_of_mem_Ioo Γ f hk i ⟨ht₁, ht₂⟩
  unfold upperAngle at ht₂
  split_ifs with h
  · simp only [h, ↓reduceDIte] at ht₂
    have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
      ⟨(nodeAngle_mem_Ico Γ f i).1.trans ht₁.le,
       ht₂.trans (nodeAngle_mem_Ico Γ f ⟨i.1 + 1, h⟩).2⟩
    rw [angleOf_cuffPoint f ht_Ico]
    exact ⟨ht₁, ht₂⟩
  · simp only [h, ↓reduceDIte] at ht₂
    by_cases hlt : t < 2 * Real.pi
    · have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨(nodeAngle_mem_Ico Γ f i).1.trans ht₁.le, by linarith⟩
      rw [angleOf_cuffPoint f ht_Ico]
      exact Or.inl ht₁
    · have ht_Ico : t - 2 * Real.pi ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨by linarith, by linarith [(nodeAngle_mem_Ico Γ f ⟨0, by omega⟩).2]⟩
      have hcp : cuffPoint f (t - 2 * Real.pi) = cuffPoint f t := cuffPoint_sub_two_pi f t
      rw [← hcp, angleOf_cuffPoint f ht_Ico]
      exact Or.inr (by linarith)

private theorem disjoint_cuffArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    {i j : Fin (Γ.N ∩ Θ).ncard} (hij : i ≠ j) :
    Disjoint (cuffArc Γ f hk i) (cuffArc Γ f hk j) := by
  have hlt_disj : ∀ {a b : Fin (Γ.N ∩ Θ).ncard}, a < b →
      Disjoint (cuffArc Γ f hk a) (cuffArc Γ f hk b) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    have ha := angleOf_mem_of_mem_cuffArc Γ f hk a hxa
    have hb := angleOf_mem_of_mem_cuffArc Γ f hk b hxb
    have ha_lt : a.1 + 1 < (Γ.N ∩ Θ).ncard := by have := b.2; omega
    simp only [ha_lt, ↓reduceDIte] at ha
    have hle1 : (⟨a.1 + 1, ha_lt⟩ : Fin (Γ.N ∩ Θ).ncard) ≤ b := hab
    have hmono1 := (strictMono_nodeAngle Γ f).monotone hle1
    have hle0 : (⟨0, by omega⟩ : Fin (Γ.N ∩ Θ).ncard) ≤ a := Nat.zero_le a.1
    have hmono0 := (strictMono_nodeAngle Γ f).monotone hle0
    split_ifs at hb with hb_lt
    · linarith
    · rcases hb with hb | hb <;> linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt_disj h
  · exact (hlt_disj h).symm

private theorem iUnion_cuffArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard) :
    (⋃ i, cuffArc Γ f hk i) = Θ \ Γ.N := by
  refine Subset.antisymm (iUnion_subset fun i => cuffArc_subset_cuff_diff_N Γ f hk i) ?_
  rintro x ⟨hxΘ, hxN⟩
  rw [mem_iUnion]
  set t := angleOf f x
  have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) := angleOf_mem_Ico f hxΘ
  have hcp : cuffPoint f t = x := cuffPoint_angleOf f hxΘ
  have hnot_range : t ∉ Set.range (nodeAngle Γ f) := by
    rw [range_nodeAngle]
    rintro ⟨y, ⟨hyN, hyΘ⟩, hy_eq⟩
    have hxy : y = x := angleOf_injOn f hyΘ hxΘ hy_eq
    exact hxN (hxy ▸ hyN)
  by_cases h0 : t < nodeAngle Γ f ⟨0, by omega⟩
  · let i_last : Fin (Γ.N ∩ Θ).ncard := ⟨(Γ.N ∩ Θ).ncard - 1, by omega⟩
    refine ⟨i_last, t + 2 * Real.pi, ?_, by rw [cuffPoint_add_two_pi, hcp]⟩
    have hi_last : ¬ (i_last.1 + 1 < (Γ.N ∩ Θ).ncard) := by dsimp [i_last]; omega
    have hup : upperAngle Γ f hk i_last = nodeAngle Γ f ⟨0, by omega⟩ + 2 * Real.pi := by
      unfold upperAngle
      simp only [hi_last, ↓reduceDIte]
    rw [hup]
    have hi_mem := (nodeAngle_mem_Ico Γ f i_last).2
    exact ⟨by linarith [ht_Ico.1], by linarith⟩
  · push Not at h0
    have h0_lt : nodeAngle Γ f ⟨0, by omega⟩ < t :=
      lt_of_le_of_ne h0 (fun h_eq => hnot_range ⟨⟨0, by omega⟩, h_eq⟩)
    let S_lt : Finset (Fin (Γ.N ∩ Θ).ncard) :=
      Finset.univ.filter (fun i => nodeAngle Γ f i < t)
    have hS_ne : S_lt.Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0_lt⟩⟩
    let i := S_lt.max' hS_ne
    have hi_mem : i ∈ S_lt := Finset.max'_mem S_lt hS_ne
    have hi_lt : nodeAngle Γ f i < t := (Finset.mem_filter.mp hi_mem).2
    refine ⟨i, t, ⟨hi_lt, ?_⟩, hcp⟩
    unfold upperAngle
    split_ifs with h
    · by_contra hge
      push Not at hge
      have hlt_next : nodeAngle Γ f ⟨i.1 + 1, h⟩ < t :=
        lt_of_le_of_ne hge (fun h_eq => hnot_range ⟨⟨i.1 + 1, h⟩, h_eq⟩)
      have hmem_next : (⟨i.1 + 1, h⟩ : Fin (Γ.N ∩ Θ).ncard) ∈ S_lt :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_next⟩
      have hle_max : (⟨i.1 + 1, h⟩ : Fin (Γ.N ∩ Θ).ncard) ≤ i :=
        Finset.le_max' S_lt _ hmem_next
      have hle_val : i.1 + 1 ≤ i.1 := hle_max
      omega
    · have h0_nonneg := (nodeAngle_mem_Ico Γ f ⟨0, by omega⟩).1
      linarith [ht_Ico.2]

private noncomputable def cuffCell (f : Circle ≃ₜ Θ) (hk : 2 ≤ (Γ.N ∩ Θ).ncard)
    (i : Fin (Γ.N ∩ Θ).ncard) : Set S :=
  pathComponentIn (Γ.U \ Γ.N) (cuffMidpoint Γ f hk i)

private theorem cuffCell_mem_C (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffCell Γ f hk i ∈ Γ.C :=
  pathComponentIn_mem_arcComponentsIn
    (cuffArc_subset_U_diff_N Γ hΘ f hk i (cuffMidpoint_mem_cuffArc Γ f hk i))

private theorem cuffArc_subset_cuffCell (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffArc Γ f hk i ⊆ cuffCell Γ f hk i :=
  subset_arcComponent_of_isPathConnected (cuffCell_mem_C Γ hΘ f hk i)
    (cuffArc_subset_U_diff_N Γ hΘ f hk i) (isPathConnected_cuffArc Γ f hk i)
    ⟨cuffMidpoint Γ f hk i, cuffMidpoint_mem_cuffArc Γ f hk i,
      mem_pathComponentIn_self (cuffArc_subset_U_diff_N Γ hΘ f hk i
        (cuffMidpoint_mem_cuffArc Γ f hk i))⟩

private theorem cuffCell_inter_cuff_nonempty (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) (i : Fin (Γ.N ∩ Θ).ncard) :
    (cuffCell Γ f hk i ∩ Θ).Nonempty :=
  ⟨cuffMidpoint Γ f hk i,
    cuffArc_subset_cuffCell Γ hΘ f hk i (cuffMidpoint_mem_cuffArc Γ f hk i),
    cuffPoint_mem f (cuffMidAngle Γ f hk i)⟩

private theorem cuffCell_tilde (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) (i : Fin (Γ.N ∩ Θ).ncard) :
    tilde (cuffCell Γ f hk i) =
      {cuffNode Γ f i, cuffNode Γ f ⟨(i.1 + 1) % (Γ.N ∩ Θ).ncard, Nat.mod_lt _ (by omega)⟩} := by
  have hc : cuffCell Γ f hk i ∈ Γ.C := cuffCell_mem_C Γ hΘ f hk i
  have hinter : (cuffCell Γ f hk i ∩ Θ).Nonempty := cuffCell_inter_cuff_nonempty Γ hΘ f hk i
  have hsub_cuff := Γ.border_cell_subset_cuff hc hΘ hinter
  have hbd : (cuffCell Γ f hk i ∩ bd S).Nonempty := by rw [hsub_cuff.2.1]; exact hinter
  obtain ⟨hncard, hfin, _, _⟩ := Γ.border_cell (cuffCell Γ f hk i) hc hbd
  have hlt := nodeAngle_lt_upperAngle Γ f hk i
  have hcl_sub : cuffPoint f '' Icc (nodeAngle Γ f i) (upperAngle Γ f hk i) ⊆
      closure (cuffCell Γ f hk i) := by
    rw [← closure_Ioo (ne_of_lt hlt)]
    exact (image_closure_subset_closure_image (cuffPoint_continuous f)).trans
      (closure_mono (cuffArc_subset_cuffCell Γ hΘ f hk i))
  have hnode1_cl : cuffNode Γ f i ∈ closure (cuffCell Γ f hk i) :=
    hcl_sub ⟨nodeAngle Γ f i, left_mem_Icc.mpr hlt.le, rfl⟩
  let j : Fin (Γ.N ∩ Θ).ncard := ⟨(i.1 + 1) % (Γ.N ∩ Θ).ncard, Nat.mod_lt _ (by omega)⟩
  have hnode2_cl : cuffNode Γ f j ∈ closure (cuffCell Γ f hk i) := by
    rw [← cuffPoint_upperAngle Γ f hk i]
    exact hcl_sub ⟨upperAngle Γ f hk i, right_mem_Icc.mpr hlt.le, rfl⟩
  have hnode_notMem : ∀ m : Fin (Γ.N ∩ Θ).ncard, cuffNode Γ f m ∉ cuffCell Γ f hk i := by
    intro m hm
    have hmN : cuffNode Γ f m ∈ Γ.N := by
      have : cuffNode Γ f m ∈ Set.range (cuffNode Γ f) := mem_range_self m
      rw [range_cuffNode] at this
      exact this.1
    exact (Γ.cell_subset_diff hc hm).2 hmN
  have hpair_sub : {cuffNode Γ f i, cuffNode Γ f j} ⊆ tilde (cuffCell Γ f hk i) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨hnode1_cl, hnode_notMem i⟩
    · exact ⟨hnode2_cl, hnode_notMem j⟩
  have hij : i ≠ j := by
    intro h_eq
    have hval : i.1 = (i.1 + 1) % (Γ.N ∩ Θ).ncard := congrArg Fin.val h_eq
    have hi_lt := i.2
    by_cases h1 : i.1 + 1 < (Γ.N ∩ Θ).ncard
    · rw [Nat.mod_eq_of_lt h1] at hval; omega
    · have heq : i.1 + 1 = (Γ.N ∩ Θ).ncard := by omega
      rw [heq, Nat.mod_self] at hval; omega
  have hne : cuffNode Γ f i ≠ cuffNode Γ f j :=
    fun h => hij (injective_cuffNode Γ f h)
  have hpair_ncard : ({cuffNode Γ f i, cuffNode Γ f j} : Set S).ncard = 2 := ncard_pair hne
  exact (eq_of_subset_of_ncard_le hpair_sub (by omega) hfin).symm

/-- For every border cell $c \in C(\Gamma)$ meeting a cuff $\Theta$, $c \cap \Theta$ is
path-connected. -/
theorem Painting.isPathConnected_cell_inter_cuff {c Θ : Set S} (hc : c ∈ Γ.C)
    (hΘ : Θ ∈ cuffs S) (hinter : (c ∩ Θ).Nonempty) :
    IsPathConnected (c ∩ Θ) := by
  have hsub := Γ.border_cell_subset_cuff hc hΘ hinter
  have hbd : (c ∩ bd S).Nonempty := by rw [hsub.2.1]; exact hinter
  obtain ⟨u, v, _, _, hL, hdiff, _, _⟩ := Γ.border_cell_exists_ends hc hbd
  rw [← hsub.2.1, hdiff]
  exact (isPathConnected_diff_ends_of_isLineWithEnds hL).2

private theorem range_cuffCell (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) :
    Set.range (cuffCell Γ f hk) = {c ∈ Γ.C | (c ∩ Θ).Nonempty} := by
  ext c
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨cuffCell_mem_C Γ hΘ f hk i, cuffCell_inter_cuff_nonempty Γ hΘ f hk i⟩
  · rintro ⟨hc, x, hxc, hxΘ⟩
    have hxN : x ∉ Γ.N := (Γ.cell_subset_diff hc hxc).2
    have hx_union : x ∈ ⋃ i, cuffArc Γ f hk i := by
      rw [iUnion_cuffArc]
      exact ⟨hxΘ, hxN⟩
    rw [mem_iUnion] at hx_union
    rcases hx_union with ⟨i, hxi⟩
    refine ⟨i, ?_⟩
    exact Γ.cell_eq_of_mem (cuffCell_mem_C Γ hΘ f hk i) hc
      (cuffArc_subset_cuffCell Γ hΘ f hk i hxi) hxc

private theorem cuffCell_inter_cuff_eq_cuffArc (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) (i : Fin (Γ.N ∩ Θ).ncard) :
    cuffCell Γ f hk i ∩ Θ = cuffArc Γ f hk i := by
  refine Subset.antisymm ?_ (fun x hx => ⟨cuffArc_subset_cuffCell Γ hΘ f hk i hx,
    (cuffArc_subset_cuff_diff_N Γ f hk i hx).1⟩)
  have : T2Space Θ := f.t2Space
  let closedArcΘ : Fin (Γ.N ∩ Θ).ncard → Set Θ := fun j =>
    (fun t : ℝ => f (Circle.exp t)) '' Icc (nodeAngle Γ f j) (upperAngle Γ f hk j)
  have hclosed : ∀ j, IsClosed (closedArcΘ j) := fun j =>
    (isCompact_Icc.image (f.continuous.comp Circle.exp.continuous)).isClosed
  have hmem_cuffArc_of_closedArcΘ : ∀ j (z : Θ), z ∈ closedArcΘ j → z.1 ∉ Γ.N →
      z.1 ∈ cuffArc Γ f hk j := by
    rintro j z ⟨t, ⟨ht₁, ht₂⟩, rfl⟩ hzN
    have hne1 : t ≠ nodeAngle Γ f j := by
      rintro rfl
      have : cuffNode Γ f j ∈ Γ.N := by
        have hmem : cuffNode Γ f j ∈ Set.range (cuffNode Γ f) := mem_range_self j
        rw [range_cuffNode] at hmem
        exact hmem.1
      exact hzN this
    have hne2 : t ≠ upperAngle Γ f hk j := by
      rintro rfl
      have hcp : (f (Circle.exp (upperAngle Γ f hk j))).1 ∈ Γ.N := by
        change cuffPoint f (upperAngle Γ f hk j) ∈ Γ.N
        rw [cuffPoint_upperAngle]
        have hmem : cuffNode Γ f ⟨(j.1 + 1) % (Γ.N ∩ Θ).ncard, Nat.mod_lt _ (by omega)⟩ ∈
            Set.range (cuffNode Γ f) := mem_range_self _
        rw [range_cuffNode] at hmem
        exact hmem.1
      exact hzN hcp
    exact ⟨t, ⟨lt_of_le_of_ne ht₁ hne1.symm, lt_of_le_of_ne ht₂ hne2⟩, rfl⟩
  let s : Set Θ := Subtype.val ⁻¹' (cuffCell Γ f hk i ∩ Θ)
  have hs_img : Subtype.val '' s = cuffCell Γ f hk i ∩ Θ := by
    ext y
    constructor
    · rintro ⟨_, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hy.2⟩, hy, rfl⟩
  have hs_conn : IsPreconnected (cuffCell Γ f hk i ∩ Θ) :=
    (Γ.isPathConnected_cell_inter_cuff (cuffCell_mem_C Γ hΘ f hk i) hΘ
      (cuffCell_inter_cuff_nonempty Γ hΘ f hk i)).isConnected.isPreconnected
  have hs_pre : IsPreconnected s := by
    rwa [← Topology.IsEmbedding.subtypeVal.isInducing.isPreconnected_image, hs_img]
  let t₁ : Set Θ := closedArcΘ i
  let t₂ : Set Θ := ⋃ j ∈ ({j : Fin (Γ.N ∩ Θ).ncard | j ≠ i} : Set _), closedArcΘ j
  have ht₁_closed : IsClosed t₁ := hclosed i
  have ht₂_closed : IsClosed t₂ :=
    (Set.toFinite _).isClosed_biUnion (fun j _ => hclosed j)
  have hs_notN : ∀ z ∈ s, z.1 ∉ Γ.N :=
    fun z hz => (Γ.cell_subset_diff (cuffCell_mem_C Γ hΘ f hk i) hz.1).2
  have hs_sub : s ⊆ t₁ ∪ t₂ := by
    intro z hz
    have hz_union : z.1 ∈ ⋃ j, cuffArc Γ f hk j := by
      rw [iUnion_cuffArc]
      exact ⟨z.2, hs_notN z hz⟩
    rw [mem_iUnion] at hz_union
    rcases hz_union with ⟨j, t, ht, hzt⟩
    have hz_cl : z ∈ closedArcΘ j :=
      ⟨t, Ioo_subset_Icc_self ht, Subtype.ext hzt⟩
    by_cases hij : j = i
    · left; subst hij; exact hz_cl
    · right; exact mem_biUnion hij hz_cl
  have h_mid : (⟨cuffMidpoint Γ f hk i, cuffPoint_mem f (cuffMidAngle Γ f hk i)⟩ : Θ) ∈ s ∩ t₁ := by
    refine ⟨⟨cuffArc_subset_cuffCell Γ hΘ f hk i (cuffMidpoint_mem_cuffArc Γ f hk i),
      cuffPoint_mem f (cuffMidAngle Γ f hk i)⟩, ?_⟩
    exact ⟨cuffMidAngle Γ f hk i, Ioo_subset_Icc_self (cuffMidAngle_mem_Ioo Γ f hk i), rfl⟩
  intro x hx
  let z : Θ := ⟨x, hx.2⟩
  have hzs : z ∈ s := hx
  rcases hs_sub hzs with hzt₁ | hzt₂
  · exact hmem_cuffArc_of_closedArcΘ i z hzt₁ (hs_notN z hzs)
  · exfalso
    obtain ⟨w, hws, hwt₁, hwt₂⟩ :=
      isPreconnected_closed_iff.mp hs_pre t₁ t₂ ht₁_closed ht₂_closed hs_sub ⟨_, h_mid⟩ ⟨z, hzs,
        hzt₂⟩
    rw [mem_iUnion₂] at hwt₂
    rcases hwt₂ with ⟨j, hji, hwj⟩
    have hwi : w.1 ∈ cuffArc Γ f hk i := hmem_cuffArc_of_closedArcΘ i w hwt₁ (hs_notN w hws)
    have hwj' : w.1 ∈ cuffArc Γ f hk j := hmem_cuffArc_of_closedArcΘ j w hwj (hs_notN w hws)
    exact Set.disjoint_left.mp (disjoint_cuffArc Γ f hk (Ne.symm hji)) hwi hwj'

private theorem injective_cuffCell (hΘ : Θ ∈ cuffs S) (f : Circle ≃ₜ Θ)
    (hk : 2 ≤ (Γ.N ∩ Θ).ncard) :
    Function.Injective (cuffCell Γ f hk) := by
  intro i j h
  by_contra hij
  have h_eq : cuffArc Γ f hk i = cuffArc Γ f hk j := by
    rw [← cuffCell_inter_cuff_eq_cuffArc Γ hΘ f hk i,
        ← cuffCell_inter_cuff_eq_cuffArc Γ hΘ f hk j, h]
  have hmid : cuffMidpoint Γ f hk i ∈ cuffArc Γ f hk j :=
    h_eq ▸ cuffMidpoint_mem_cuffArc Γ f hk i
  exact Set.disjoint_left.mp (disjoint_cuffArc Γ f hk hij)
    (cuffMidpoint_mem_cuffArc Γ f hk i) hmid

/-- Every cuff $\Theta$ of a surface $S$ that is an O-arc admits a cyclic enumeration
$n_1, c_1, n_2, c_2, \dots, n_k, c_k, (n_1)$ of the nodes and cells of $\Gamma$ bordering $\Theta$,
with $k = |N(\Gamma) \cap \Theta| \ge 2$.
Graph Minors XVII, Section 2 (pages 165–166), Section 4 (page 170), and Section 10 (page 188). -/
theorem Painting.exists_cuffEnumeration (hΘ : Θ ∈ cuffs S) (hΘ_arc : IsOArc Θ) :
    Nonempty (Γ.CuffEnumeration Θ (Γ.N ∩ Θ).ncard) := by
  obtain ⟨f⟩ := hΘ_arc
  have hk : 2 ≤ (Γ.N ∩ Θ).ncard := Γ.two_le_ncard_nodes_inter_cuff hΘ ⟨f⟩
  exact ⟨{
    cuff_mem := hΘ
    two_le := hk
    node := cuffNode Γ f
    cell := cuffCell Γ f hk
    injective_node := injective_cuffNode Γ f
    injective_cell := injective_cuffCell Γ hΘ f hk
    range_node := range_cuffNode Γ f
    range_cell := range_cuffCell Γ hΘ f hk
    cell_tilde := cuffCell_tilde Γ hΘ f hk
    nodes_in_order := cuffNode_inOrderOn Γ f
  }⟩

end CuffEnumeration

end GraphMinor.GM17
