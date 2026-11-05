/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

public import LeanPool.LCAnalysis.MichalBastiani

/-!
# Higher differentials

Glöckner–Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362), §1.3.

The `k`-th differential of `f : E → F` is
`d^(k) f (x, y₁, …, yₖ) = (D_{yₖ} ⋯ D_{y₁} f)(x)` (`iteratedDMB`). We show:

* Proposition 1.3.10: `f` is `C^k` in the recursive sense of `ContDiffMBOn` if and only if `f`
  is continuous and the differentials `d^(j) f` exist and are continuous on `U × E^j` for
  `j ≤ k` (the original definition of Bastiani and Neeb, `HasContIterDerivOn`).
* Remark 1.3.13: if `f` is `C^r`, then `d^(k) f` is `C^{r-k}` on `U × E^k`.
* Proposition 1.3.17 (Schwarz): for `f` of class `C^k`, `d^(k) f (x, ·)` is a continuous,
  symmetric `k`-linear map.
-/

@[expose] public section

open Set Filter Function
open scoped Topology


noncomputable section

namespace LCAnalysis

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F]

/-- The `k`-th differential `d^(k) f (x, y) = (D_{y (k-1)} ⋯ D_{y 0} f)(x)`
(junk values where the derivatives do not exist). -/
def iteratedDMB : (k : ℕ) → (E → F) → E × (Fin k → E) → F
  | 0, f, p => f p.1
  | k + 1, f, p => dMB (fun z ↦ iteratedDMB k f (z, Fin.init p.2)) (p.1, p.2 (Fin.last k))

/-- Neeb's definition of `C^k` maps: the iterated directional derivatives `d^(j) f` exist for
`j ≤ k` and are continuous on `U × E^j` (for `j = 0`, this is the continuity of `f`). -/
def HasContIterDerivOn (k : ℕ) (f : E → F) (U : Set E) : Prop :=
  (∀ j < k, ∀ x ∈ U, ∀ v : Fin (j + 1) → E, HasDirDerivAt (fun z ↦ iteratedDMB j f (z, Fin.init v))
    x (v (Fin.last j)) (iteratedDMB (j + 1) f (x, v))) ∧
  ∀ j ≤ k, ContinuousOn (iteratedDMB j f) (U ×ˢ univ)

/-! ### Algebraic identities -/

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
theorem iteratedDMB_zero (f : E → F) (p : E × (Fin 0 → E)) : iteratedDMB 0 f p = f p.1 := rfl

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
theorem iteratedDMB_one (f : E → F) (x : E) (v : Fin 1 → E) :
    iteratedDMB 1 f (x, v) = dMB f (x, v 0) := rfl

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
theorem iteratedDMB_succ (k : ℕ) (f : E → F) (x : E) (v : Fin (k + 1) → E) :
    iteratedDMB (k + 1) f (x, v) =
      dMB (fun z ↦ iteratedDMB k f (z, Fin.init v)) (x, v (Fin.last k)) := rfl

private theorem init_cons {n : ℕ} {α : Type*} (a : α) (v : Fin (n + 1) → α) :
    Fin.init (Fin.cons a v : Fin (n + 2) → α) = Fin.cons a (Fin.init v) := by
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> rfl

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
/-- Peeling off the first direction:
`d^(k+1) f (x, y, v) = d^(k) (df(·, y)) (x, v)`. -/
theorem iteratedDMB_cons : ∀ (k : ℕ) (f : E → F) (y x : E) (v : Fin k → E),
    iteratedDMB (k + 1) f (x, Fin.cons y v) = iteratedDMB k (fun z ↦ dMB f (z, y)) (x, v)
  | 0, _, _, _, _ => rfl
  | k + 1, f, y, x, v => by
    rw [iteratedDMB_succ, iteratedDMB_succ, init_cons]
    simp only [iteratedDMB_cons k]
    rfl

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
theorem dMB_slice {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    (g : E × E' → F) (x h : E) (a : E') :
    dMB g ((x, a), (h, 0)) = dMB (fun z ↦ g (z, a)) (x, h) := by
  simp only [dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
/-- Derivatives in directions `(0, b)` are derivatives of the second slice. -/
theorem dMB_slice₂ {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    (g : E × E' → F) (x : E) (a b : E') :
    dMB g ((x, a), (0, b)) = dMB (fun w ↦ g (x, w)) (a, b) := by
  simp only [dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
theorem hasDirDerivAt_slice {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    {g : E × E' → F} {x h : E} {a : E'} {y : F} :
    HasDirDerivAt g (x, a) (h, 0) y ↔ HasDirDerivAt (fun z ↦ g (z, a)) x h y := by
  simp only [HasDirDerivAt, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
/-- Differentials of a slice `z ↦ g (z, a)` are differentials of `g` in directions `(y, 0)`. -/
theorem iteratedDMB_slice {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] :
    ∀ (k : ℕ) (g : E × E' → F) (a : E') (x : E) (v : Fin k → E),
    iteratedDMB k (fun z ↦ g (z, a)) (x, v) = iteratedDMB k g ((x, a), fun i ↦ (v i, 0))
  | 0, _, _, _, _ => rfl
  | k + 1, g, a, x, v => by
    rw [iteratedDMB_succ, iteratedDMB_succ, dMB_slice]
    simp only [iteratedDMB_slice k]
    rfl

omit [ContinuousSMul ℝ F] in
/-- Glöckner–Neeb (1.36): `d^(k+1) f (x, y₀, …, yₖ) = d^(k) (df) ((x, y₀), (y₁, 0), …, (yₖ, 0))`. -/
theorem iteratedDMB_succ_eq_dMB (k : ℕ) (f : E → F) (x : E) (v : Fin (k + 1) → E) :
    iteratedDMB (k + 1) f (x, v) = iteratedDMB k (dMB f) ((x, v 0), fun i ↦ (v i.succ, 0)) := by
  rw [← Fin.cons_self_tail v, iteratedDMB_cons, iteratedDMB_slice]
  rfl

/-! ### Proposition 1.3.10, first half -/

omit [ContinuousSMul ℝ F] in
theorem ContinuousOn.iteratedDMB_zero {f : E → F} {U : Set E} (hf : ContinuousOn f U) :
    ContinuousOn (iteratedDMB 0 f) (U ×ˢ univ) :=
  hf.comp continuousOn_fst fun _ hp ↦ hp.1

omit [ContinuousSMul ℝ F] in
/-- A `C^k` map has continuous differentials `d^(j) f` for `j ≤ k`. -/
theorem ContDiffMBOn.hasContIterDerivOn : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁]
    [Module ℝ E₁] [TopologicalSpace E₁] {f : E₁ → F} {U : Set E₁},
    ContDiffMBOn k f U → HasContIterDerivOn k f U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ f U hf
    refine ⟨fun j hj ↦ absurd hj (Nat.not_lt_zero j), fun j hj ↦ ?_⟩
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact ContinuousOn.iteratedDMB_zero hf
  | succ k ih =>
    intro E₁ _ _ _ f U hf
    obtain ⟨hc, hd, hdf⟩ := hf
    obtain ⟨N₁, N₂⟩ := ih hdf
    refine ⟨fun j hj x hx v ↦ ?_, fun j hj ↦ ?_⟩
    · cases j with
      | zero => exact hd x hx (v (Fin.last 0))
      | succ j =>
        have h1 := N₁ j (by omega) (x, v 0) ⟨hx, mem_univ _⟩ (fun i ↦ (v i.succ, 0))
        rw [← iteratedDMB_succ_eq_dMB] at h1
        have h2 := hasDirDerivAt_slice.mp h1
        have e : (fun z ↦ iteratedDMB (j + 1) f (z, Fin.init v)) =
            fun z ↦ iteratedDMB j (dMB f) ((z, v 0), Fin.init fun i ↦ (v i.succ, (0 : E₁))) :=
          funext fun z ↦ iteratedDMB_succ_eq_dMB j f z _
        rw [e]
        exact h2
    · cases j with
      | zero => exact ContinuousOn.iteratedDMB_zero hc
      | succ j =>
        have h1 : ContinuousOn (iteratedDMB j (dMB f)) ((U ×ˢ univ) ×ˢ univ) := N₂ j (by omega)
        have e : iteratedDMB (j + 1) f =
            fun p ↦ iteratedDMB j (dMB f) ((p.1, p.2 0), fun i ↦ (p.2 i.succ, (0 : E₁))) :=
          funext fun p ↦ iteratedDMB_succ_eq_dMB j f p.1 p.2
        rw [e]
        exact h1.comp (by fun_prop) fun p hp ↦ ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩

omit [TopologicalSpace E] [ContinuousSMul ℝ F] in
theorem hasDirDerivAt_slice₂ {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    {g : E × E' → F} {x : E} {a h : E'} {y : F} :
    HasDirDerivAt g (x, a) (0, h) y ↔ HasDirDerivAt (fun w ↦ g (x, w)) a h y := by
  simp only [HasDirDerivAt, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

omit [ContinuousSMul ℝ F] in
/-- The directional derivative of a continuous map that is additive and homogeneous in each
variable separately: `D_h M (w) = ∑ᵢ M (w₁, …, hᵢ, …, wₗ)`. -/
theorem hasDirDerivAt_of_multilinear {ℓ : ℕ} {M : (Fin ℓ → E) → F}
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup F] (hM : Continuous M)
    (hadd : ∀ w i (a b : E), M (update w i (a + b)) = M (update w i a) + M (update w i b))
    (hsmul : ∀ w i (c : ℝ) (a : E), M (update w i (c • a)) = c • M (update w i a))
    (w h : Fin ℓ → E) : HasDirDerivAt M w h (∑ i, M (update w i (h i))) := by
  let m : ℝ → ℕ → Fin ℓ → E := fun t n j ↦ if (j : ℕ) < n then w j + t • h j else w j
  have hm : ∀ n, Continuous fun t ↦ m t n := fun n ↦ continuous_pi fun j ↦ by
    by_cases hj : (j : ℕ) < n
    · simp only [m, hj, ite_true]; fun_prop
    · simp only [m, hj, ite_false]; fun_prop
  have hstep : ∀ t (i : Fin ℓ), M (m t (i + 1)) - M (m t i) = t • M (update (m t i) i (h i)) := by
    intro t i
    have e1 : m t (i + 1) = update (m t i) i (w i + t • h i) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [m]
      · have : ((j : ℕ) < i + 1 ↔ (j : ℕ) < i) := by
          have := Fin.val_ne_of_ne hj; omega
        simp only [m, update_of_ne hj, this]
    have e2 : m t i = update (m t i) i (w i) := by
      conv_lhs => rw [← update_eq_self i (m t i)]
      simp [m]
    rw [e1, hadd, hsmul, ← e2, add_sub_cancel_left]
  have hkey : ∀ t, M (w + t • h) - M w = t • ∑ i : Fin ℓ, M (update (m t i) i (h i)) := by
    intro t
    have hl : m t ℓ = w + t • h := by funext j; simp [m, j.isLt]
    have h0 : m t 0 = w := by funext j; simp [m]
    rw [Finset.smul_sum, ← hl, ← h0, ← Finset.sum_range_sub (fun n ↦ M (m t n)),
      ← Fin.sum_univ_eq_sum_range (fun n ↦ M (m t (n + 1)) - M (m t n))]
    exact Finset.sum_congr rfl fun i _ ↦ hstep t i
  have hc : Continuous fun t ↦ ∑ i : Fin ℓ, M (update (m t i) i (h i)) :=
    continuous_finsetSum _ fun i _ ↦ hM.comp ((hm i).update i continuous_const)
  have h0 : (∑ i : Fin ℓ, M (update (m 0 i) i (h i))) = ∑ i, M (update w i (h i)) := by
    congr 1; funext i; congr 2; funext j; simp [m]
  rw [HasDirDerivAt, ← h0]
  refine ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  rw [hkey, smul_smul, inv_mul_cancel₀ ht, one_smul]

omit [ContinuousSMul ℝ F] in
theorem HasDirDerivAt.add {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [IsTopologicalAddGroup F] {f g : E₁ → F} {x h : E₁} {a b : F} (hf : HasDirDerivAt f x h a)
    (hg : HasDirDerivAt g x h b) : HasDirDerivAt (fun y ↦ f y + g y) x h (a + b) :=
  (Filter.Tendsto.add hf hg).congr fun t ↦ by simp only [← smul_add]; congr 1; abel

theorem HasDirDerivAt.const_smul {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
     {f : E₁ → F} {x h : E₁} {a : F} (hf : HasDirDerivAt f x h a) (c : ℝ) :
    HasDirDerivAt (fun y ↦ c • f y) x h (c • a) :=
  (Filter.Tendsto.const_smul hf c).congr fun t ↦ by
    beta_reduce; rw [smul_comm c t⁻¹, smul_sub]

/-! ### Proposition 1.3.10, second half -/

section LocallyConvex

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
theorem contDiffMBOn_const : ∀ (k : ℕ) {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] (c : F) (U : Set E₁),
    ContDiffMBOn k (fun _ : E₁ ↦ c) U := by
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ c U; exact continuousOn_const
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ c U
    have hd : ∀ x h : E₁, HasDirDerivAt (fun _ : E₁ ↦ c) x h 0 := fun x h ↦ by
      simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
    have heq : dMB (fun _ : E₁ ↦ c) = fun _ ↦ 0 := funext fun p ↦ (hd p.1 p.2).dMB_eq
    refine ⟨continuousOn_const, fun x _ h ↦ ?_, ?_⟩
    · rw [heq]; exact hd x h
    · rw [heq]; exact ih 0 _

theorem ContDiffMBOn.add {k : ℕ} {f g : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) : ContDiffMBOn k (fun x ↦ f x + g x) U :=
  ContDiffMBOn.comp (F₁ := F × F) hU isOpen_univ
    ((ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ)
    (ContDiffMBOn.prodMk hU hf hg) (mapsTo_univ _ _)

theorem ContDiffMBOn.sum {k : ℕ} {ι : Type*} (s : Finset ι) {f : ι → E → F} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i ∈ s, ContDiffMBOn k (f i) U) :
    ContDiffMBOn k (fun x ↦ ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using contDiffMBOn_const k (0 : F) U
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add hU
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- `((x, w), (y, h)) ↦ (x, w₁, …, hᵢ, …, wₗ)`. -/
private def updateCLM (ℓ : ℕ) (i : Fin ℓ) :
    (E × (Fin ℓ → E)) × (E × (Fin ℓ → E)) →L[ℝ] E × (Fin ℓ → E) where
  toFun q := (q.1.1, update q.1.2 i (q.2.2 i))
  map_add' q q' := by
    refine Prod.ext rfl (funext fun j ↦ ?_)
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, update_apply]
    split_ifs <;> rfl
  map_smul' c q := by
    refine Prod.ext rfl (funext fun j ↦ ?_)
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, update_apply, RingHom.id_apply]
    split_ifs <;> rfl
  cont := (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).update i
    ((continuous_apply i).comp (continuous_snd.comp continuous_snd)))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
@[simp] private theorem updateCLM_apply (ℓ : ℕ) (i : Fin ℓ) (q) :
    updateCLM (E := E) ℓ i q = (q.1.1, update q.1.2 i (q.2.2 i)) := rfl

/-- `((x, w), (y, h)) ↦ (x, y, w₁, …, wₗ)`. -/
private def consCLM (ℓ : ℕ) :
    (E × (Fin ℓ → E)) × (E × (Fin ℓ → E)) →L[ℝ] E × (Fin (ℓ + 1) → E) where
  toFun q := (q.1.1, Fin.cons q.2.1 q.1.2)
  map_add' q q' := by
    refine Prod.ext rfl (funext fun j ↦ ?_)
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
  map_smul' c q := by
    refine Prod.ext rfl (funext fun j ↦ ?_)
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
  cont := (continuous_fst.comp continuous_fst).prodMk
    (Continuous.finCons (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_fst))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
@[simp] private theorem consCLM_apply (ℓ : ℕ) (q) :
    consCLM (E := E) ℓ q = (q.1.1, Fin.cons q.2.1 q.1.2) := rfl

/-- Glöckner–Neeb, Lemma 1.3.12: a map `f : U × E^ℓ → F` that is `ℓ`-linear in the second
variable and has continuous differentials `d^(j)` in the first variable for `j ≤ r` is `C^r`. -/
theorem contDiffMBOn_of_multilinear {U : Set E} (hU : IsOpen U) : ∀ (r ℓ : ℕ)
    (f : E × (Fin ℓ → E) → F),
    (∀ x ∈ U, ∀ w i (a b : E),
      f (x, update w i (a + b)) = f (x, update w i a) + f (x, update w i b)) →
    (∀ x ∈ U, ∀ w i (c : ℝ) (a : E), f (x, update w i (c • a)) = c • f (x, update w i a)) →
    (∀ j < r, ∀ x ∈ U, ∀ w, ∀ v : Fin (j + 1) → E,
      HasDirDerivAt (fun z ↦ iteratedDMB j (fun z' ↦ f (z', w)) (z, Fin.init v)) x (v (Fin.last j))
        (iteratedDMB (j + 1) (fun z' ↦ f (z', w)) (x, v))) →
    (∀ j ≤ r, ContinuousOn (fun q : (E × (Fin ℓ → E)) × (Fin j → E) ↦
      iteratedDMB j (fun z ↦ f (z, q.1.2)) (q.1.1, q.2)) ((U ×ˢ univ) ×ˢ univ)) →
    ContDiffMBOn r f (U ×ˢ univ) := by
  have hc0 : ∀ (ℓ : ℕ) (f : E × (Fin ℓ → E) → F), ContinuousOn
      (fun q : (E × (Fin ℓ → E)) × (Fin 0 → E) ↦ iteratedDMB 0 (fun z ↦ f (z, q.1.2)) (q.1.1, q.2))
      ((U ×ˢ univ) ×ˢ univ) → ContinuousOn f (U ×ˢ univ) := fun ℓ f h ↦
    h.comp (continuous_id.prodMk continuous_const).continuousOn
      fun p hp ↦ ⟨hp, mem_univ (Fin.elim0 : Fin 0 → E)⟩
  intro r
  induction r with
  | zero => intro ℓ f _ _ _ hcont; exact hc0 ℓ f (hcont 0 le_rfl)
  | succ r ih =>
    intro ℓ f hadd hsmul hex hcont
    have hc : ContinuousOn f (U ×ˢ univ) := hc0 ℓ f (hcont 0 (Nat.zero_le _))
    have hUW : IsOpen (U ×ˢ (univ : Set (Fin ℓ → E))) := hU.prod isOpen_univ
    have hd1 : ∀ x ∈ U, ∀ w y, HasDirDerivAt (fun z ↦ f (z, w)) x y
        (dMB (fun z ↦ f (z, w)) (x, y)) :=
      fun x hx w y ↦ hex 0 (Nat.succ_pos r) x hx w (fun _ ↦ y)
    have hφ1 : Continuous fun q : (E × (Fin ℓ → E)) × E ↦ (q.1, fun _ : Fin 1 ↦ q.2) := by
      fun_prop
    have hc1' := (hcont 1 (by omega)).comp hφ1.continuousOn
      fun q (hq : q ∈ (U ×ˢ univ) ×ˢ (univ : Set E)) ↦ ⟨hq.1, mem_univ _⟩
    have hc1 : ContinuousOn
        (fun q : (E × (Fin ℓ → E)) × E ↦ dMB (fun z ↦ f (z, q.1.2)) (q.1.1, q.2))
        ((U ×ˢ univ) ×ˢ univ) := hc1'.congr fun q _ ↦ by
      simp only [Function.comp_apply, iteratedDMB_one]
    have hslice : ∀ w, ContDiffMBOn 1 (fun z ↦ f (z, w)) U := by
      intro w
      have e1 : Continuous fun z : E ↦ (z, w) := by fun_prop
      have e2 : Continuous fun p : E × E ↦ ((p.1, w), p.2) := by fun_prop
      refine ⟨hc.comp e1.continuousOn fun z hz ↦ ⟨hz, mem_univ _⟩, fun x hx y ↦ hd1 x hx w y, ?_⟩
      change ContinuousOn (dMB fun z ↦ f (z, w)) (U ×ˢ univ)
      refine (hc1.comp e2.continuousOn ?_).congr fun p _ ↦ ?_
      · intro p hp; exact ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩
      · rfl
    have dadd : ∀ x ∈ U, ∀ w i (a b y : E), dMB (fun z ↦ f (z, update w i (a + b))) (x, y) =
        dMB (fun z ↦ f (z, update w i a)) (x, y) + dMB (fun z ↦ f (z, update w i b)) (x, y) := by
      intro x hx w i a b y
      have hs : HasDirDerivAt (fun z ↦ f (z, update w i a) + f (z, update w i b)) x y
          (dMB (fun z ↦ f (z, update w i a)) (x, y) + dMB (fun z ↦ f (z, update w i b)) (x, y)) :=
        (hd1 x hx _ y).add (hd1 x hx _ y)
      have heq : (fun z ↦ f (z, update w i a) + f (z, update w i b)) =ᶠ[𝓝 x]
          fun z ↦ f (z, update w i (a + b)) := by
        filter_upwards [hU.mem_nhds hx] with z hz
        exact (hadd z hz w i a b).symm
      exact (hs.congr_of_eventuallyEq heq).dMB_eq
    have dsmul : ∀ x ∈ U, ∀ w i (c : ℝ) (a y : E), dMB (fun z ↦ f (z, update w i (c • a))) (x, y) =
        c • dMB (fun z ↦ f (z, update w i a)) (x, y) := by
      intro x hx w i c a y
      have hs : HasDirDerivAt (fun z ↦ c • f (z, update w i a)) x y
          (c • dMB (fun z ↦ f (z, update w i a)) (x, y)) := (hd1 x hx _ y).const_smul c
      have heq : (fun z ↦ c • f (z, update w i a)) =ᶠ[𝓝 x] fun z ↦ f (z, update w i (c • a)) := by
        filter_upwards [hU.mem_nhds hx] with z hz
        exact (hsmul z hz w i c a).symm
      exact (hs.congr_of_eventuallyEq heq).dMB_eq
    obtain ⟨h1, hdf⟩ := contDiffMBOn_one_of_partials hUW
      (d₁ := fun p y ↦ dMB (fun z ↦ f (z, p.2)) (p.1, y))
      (d₂ := fun p h ↦ ∑ i, f (p.1, update p.2 i (h i)))
      (fun p hp y ↦ hasDirDerivAt_slice.mpr (hd1 p.1 hp.1 p.2 y))
      (fun p hp h ↦ hasDirDerivAt_slice₂.mpr (hasDirDerivAt_of_multilinear
        (M := fun w ↦ f (p.1, w))
        (hc.comp_continuous (by fun_prop : Continuous fun w : Fin ℓ → E ↦ (p.1, w))
          fun w ↦ ⟨hp.1, mem_univ w⟩)
        (hadd p.1 hp.1) (hsmul p.1 hp.1) p.2 h))
      hc1
      (continuousOn_finsetSum _ fun i _ ↦ hc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).update i
          ((continuous_apply i).comp continuous_snd))).continuousOn
        fun q hq ↦ ⟨hq.1.1, mem_univ _⟩)
    refine ⟨hc, h1.2.1, ?_⟩
    have hfr : ContDiffMBOn r f (U ×ˢ univ) :=
      ih ℓ f hadd hsmul (fun j hj ↦ hex j (by omega)) (fun j hj ↦ hcont j (by omega))
    have hgr : ContDiffMBOn r
        (fun p : E × (Fin (ℓ + 1) → E) ↦ dMB (fun z ↦ f (z, Fin.tail p.2)) (p.1, p.2 0))
        (U ×ˢ univ) := by
      refine ih (ℓ + 1) _ ?_ ?_ ?_ ?_
      · intro x hx w' i a b
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · simp only [Fin.tail_update_zero, update_self]
          exact (hslice _).dMB_add hU hx a b
        · simp only [Fin.tail_update_succ]
          exact dadd x hx _ i a b _
      · intro x hx w' i c a
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · simp only [Fin.tail_update_zero, update_self]
          exact (hslice _).dMB_smul hx c a
        · simp only [Fin.tail_update_succ]
          exact dsmul x hx _ i c a _
      · intro j hj x hx w' v
        have := hex (j + 1) (by omega) x hx (Fin.tail w') (Fin.cons (w' 0) v)
        rw [init_cons] at this
        simp only [iteratedDMB_cons] at this
        exact this
      · intro j hj
        have hcj := hcont (j + 1) (by omega)
        have hφ : Continuous fun q : (E × (Fin (ℓ + 1) → E)) × (Fin j → E) ↦
            ((q.1.1, Fin.tail q.1.2), (Fin.cons (q.1.2 0) q.2 : Fin (j + 1) → E)) := by
          refine ((continuous_fst.comp continuous_fst).prodMk ?_).prodMk ?_
          · exact continuous_pi fun i ↦ (continuous_apply i.succ).comp
              (continuous_snd.comp continuous_fst)
          · exact Continuous.finCons ((continuous_apply 0).comp
              (continuous_snd.comp continuous_fst)) continuous_snd
        refine (hcj.comp hφ.continuousOn fun q (hq : q ∈ (U ×ˢ (univ : Set (Fin (ℓ + 1) → E))) ×ˢ
          (univ : Set (Fin j → E))) ↦ ⟨⟨hq.1.1, mem_univ _⟩, mem_univ _⟩).congr fun q _ ↦ ?_
        simp only [Function.comp_apply, iteratedDMB_cons]
    have hG := ContDiffMBOn.comp_clm (consCLM ℓ) (hU.prod isOpen_univ) hgr
    have hF := fun i ↦ ContDiffMBOn.comp_clm (updateCLM ℓ i) hUW hfr
    have hpre₁ : (consCLM (E := E) ℓ) ⁻¹' (U ×ˢ univ) = (U ×ˢ univ) ×ˢ univ := by ext; simp
    have hpre₂ : ∀ i, (updateCLM (E := E) ℓ i) ⁻¹' (U ×ˢ univ) = (U ×ˢ univ) ×ˢ univ := by
      intro i; ext; simp
    rw [hpre₁] at hG
    simp only [hpre₂] at hF
    have hΦ := hG.add (hUW.prod isOpen_univ)
      (ContDiffMBOn.sum Finset.univ (hUW.prod isOpen_univ) fun i _ ↦ hF i)
    refine ContDiffMBOn.congr_of_isOpen (hUW.prod isOpen_univ) (fun q hq ↦ ?_) hΦ
    have := hdf q.1 hq.1 q.2.1 q.2.2
    simp only [Prod.mk.eta] at this
    rw [this]
    simp [Fin.tail_cons]

/-- Glöckner–Neeb, Proposition 1.3.10: Neeb's definition of `C^k` implies the recursive one. -/
theorem HasContIterDerivOn.contDiffMBOn {k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : HasContIterDerivOn k f U) : ContDiffMBOn k f U := by
  have h := contDiffMBOn_of_multilinear hU k 0 (fun p ↦ f p.1) (fun _ _ _ i ↦ i.elim0)
    (fun _ _ _ i ↦ i.elim0) (fun j hj x hx _ v ↦ hf.1 j hj x hx v)
    (fun j hj ↦ (hf.2 j hj).comp
      (by fun_prop : Continuous fun q : (E × (Fin 0 → E)) × (Fin j → E) ↦ (q.1.1, q.2)).continuousOn
      fun q hq ↦ ⟨hq.1.1, mem_univ _⟩)
  have h2 := ContDiffMBOn.comp_clm (ContinuousLinearMap.inl ℝ E (Fin 0 → E)) (hU.prod isOpen_univ) h
  have hpre : (ContinuousLinearMap.inl ℝ E (Fin 0 → E)) ⁻¹' (U ×ˢ univ) = U := by ext; simp
  rw [hpre] at h2
  exact h2

/-- Glöckner–Neeb, Proposition 1.3.10: the recursive definition of `C^k` agrees with Neeb's. -/
theorem contDiffMBOn_iff_hasContIterDerivOn {k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U) :
    ContDiffMBOn k f U ↔ HasContIterDerivOn k f U :=
  ⟨ContDiffMBOn.hasContIterDerivOn, HasContIterDerivOn.contDiffMBOn hU⟩

/-! ### Remark 1.3.13: the differentials of a `C^r` map are `C^{r-k}` -/

/-- `(x, y₀, …, yₖ) ↦ ((x, y₀), (y₁, 0), …, (yₖ, 0))`, see (1.36). -/
private def shiftCLM (k : ℕ) : E × (Fin (k + 1) → E) →L[ℝ] (E × E) × (Fin k → E × E) where
  toFun p := ((p.1, p.2 0), fun i ↦ (p.2 i.succ, 0))
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp
  cont := by fun_prop

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [ContinuousSMul ℝ F] in
theorem ContDiffMBOn.contDiffMBOn_iteratedDMB : ∀ (k : ℕ) {r : ℕ} {E₁ : Type u}
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
    [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U : Set E₁},
    IsOpen U → ContDiffMBOn (k + r) f U → ContDiffMBOn r (iteratedDMB k f) (U ×ˢ univ) := by
  intro k
  induction k with
  | zero =>
    intro r E₁ _ _ _ _ _ _ _ f U hU hf
    rw [zero_add] at hf
    have h := ContDiffMBOn.comp_clm (ContinuousLinearMap.fst ℝ E₁ (Fin 0 → E₁)) hU hf
    have hpre : (ContinuousLinearMap.fst ℝ E₁ (Fin 0 → E₁)) ⁻¹' U = U ×ˢ univ := by ext; simp
    rw [hpre] at h
    exact h
  | succ k ih =>
    intro r E₁ _ _ _ _ _ _ _ f U hU hf
    rw [show k + 1 + r = (k + r) + 1 by omega] at hf
    have h1 := ih (hU.prod isOpen_univ) hf.2.2
    have h2 := ContDiffMBOn.comp_clm (shiftCLM k) ((hU.prod isOpen_univ).prod isOpen_univ) h1
    have hpre : (shiftCLM (E := E₁) k) ⁻¹' ((U ×ˢ univ) ×ˢ univ) = U ×ˢ univ := by
      ext; simp [shiftCLM]
    rw [hpre] at h2
    have e : iteratedDMB (k + 1) f = iteratedDMB k (dMB f) ∘ shiftCLM k :=
      funext fun p ↦ iteratedDMB_succ_eq_dMB k f p.1 p.2
    rw [e]
    exact h2

/-- For fixed directions `w`, the map `x ↦ d^(k) f (x, w)` is `C^r` if `f` is `C^{k+r}`. -/
theorem ContDiffMBOn.contDiffMBOn_iteratedDMB_slice {k r : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffMBOn (k + r) f U) (w : Fin k → E) :
    ContDiffMBOn r (fun z ↦ iteratedDMB k f (z, w)) U := by
  have hp : ContDiffMBOn r (fun z : E ↦ (z, w)) U :=
    ContDiffMBOn.prodMk hU ((ContinuousLinearMap.id ℝ E).contDiffMBOn r U)
      (contDiffMBOn_const r w U)
  exact ContDiffMBOn.comp hU (hU.prod isOpen_univ) (hf.contDiffMBOn_iteratedDMB k hU) hp
    fun z hz ↦ ⟨hz, mem_univ _⟩

/-! ### Proposition 1.3.17: Schwarz's theorem -/

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F]
    [LocallyConvexSpace ℝ F] [T2Space F] in
theorem dMB_congr_of_eventuallyEq {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) (v : E) :
    dMB f₁ (x, v) = dMB f₂ (x, v) := by
  have hl : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[≠] 0) (𝓝 x) := by
    have : Continuous fun t : ℝ ↦ x + t • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  simp only [dMB, limUnder]
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [hl.eventually h] with t ht
  simp only [ht, h.eq_of_nhds]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F]
    [ContinuousSMul ℝ F] in
theorem iteratedDMB_add_two (k : ℕ) (f : E → F) (x : E) (v : Fin (k + 2) → E) :
    iteratedDMB (k + 2) f (x, v) = dMB (dMB fun z ↦ iteratedDMB k f (z, Fin.init (Fin.init v)))
      ((x, v (Fin.last k).castSucc), (v (Fin.last (k + 1)), 0)) := by
  rw [dMB_slice]
  rfl

/-- Swapping two adjacent directions does not change `d^(k+1) f`. -/
theorem ContDiffMBOn.iteratedDMB_swap {m : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn m f U) : ∀ (k : ℕ), k + 1 ≤ m → ∀ x ∈ U, ∀ (v : Fin (k + 1) → E)
    (i : Fin k), iteratedDMB (k + 1) f (x, v ∘ Equiv.swap i.castSucc i.succ) =
      iteratedDMB (k + 1) f (x, v) := by
  intro k
  induction k with
  | zero => intro _ x _ v i; exact i.elim0
  | succ k ih =>
    intro hk x hx v i
    by_cases hi : i = Fin.last k
    · subst hi
      rw [iteratedDMB_add_two, iteratedDMB_add_two]
      have hg : ContDiffMBOn 2 (fun z ↦ iteratedDMB k f (z, Fin.init (Fin.init v))) U :=
        (hf.of_le (show k + 2 ≤ m by omega)).contDiffMBOn_iteratedDMB_slice (k := k) (r := 2) hU _
      have e1 : Fin.init (Fin.init (v ∘ Equiv.swap (Fin.last k).castSucc (Fin.last k).succ)) =
          Fin.init (Fin.init v) := by
        funext j
        simp only [Fin.init, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne] <;> (apply Fin.ne_of_val_ne; simp; omega)
      rw [e1]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.succ_last,
        Equiv.swap_apply_right]
      exact hg.dMB_dMB_symm hU hx _ _
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      rw [iteratedDMB_succ, iteratedDMB_succ]
      have e1 : Fin.init (v ∘ Equiv.swap j.castSucc.castSucc j.castSucc.succ) =
          Fin.init v ∘ Equiv.swap j.castSucc j.succ := by
        funext m
        simp only [Fin.init, Function.comp_apply, Fin.succ_castSucc]
        rw [(Fin.castSucc_injective _).swap_apply]
      have e2 : (v ∘ Equiv.swap j.castSucc.castSucc j.castSucc.succ) (Fin.last (k + 1)) =
          v (Fin.last (k + 1)) := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne] <;> (apply Fin.ne_of_val_ne; simp; omega)
      rw [e1, e2]
      apply dMB_congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with z hz
      exact ih (by omega) z hz (Fin.init v) j

/-- Proposition 1.3.17: `d^(k) f (x, ·)` is symmetric. -/
theorem ContDiffMBOn.iteratedDMB_perm {m k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn m f U) (hk : k ≤ m) {x : E} (hx : x ∈ U) (v : Fin k → E)
    (σ : Equiv.Perm (Fin k)) : iteratedDMB k f (x, v ∘ σ) = iteratedDMB k f (x, v) := by
  cases k with
  | zero => congr 2; funext i; exact i.elim0
  | succ k =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin k ↦ Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hσ using Submonoid.closure_induction generalizing v with
    | mem τ hτ =>
      obtain ⟨i, rfl⟩ := hτ
      exact hf.iteratedDMB_swap hU k hk x hx v i
    | one => rfl
    | mul τ ρ _ _ hτ hρ =>
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hρ, hτ]

/-- Linearity of `d^(k+1) f (x, ·)` in the last direction. -/
theorem ContDiffMBOn.iteratedDMB_snoc_add {m k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn m f U) (hk : k + 1 ≤ m) {x : E} (hx : x ∈ U) (v : Fin k → E) (a b : E) :
    iteratedDMB (k + 1) f (x, Fin.snoc v (a + b)) =
      iteratedDMB (k + 1) f (x, Fin.snoc v a) + iteratedDMB (k + 1) f (x, Fin.snoc v b) := by
  simp only [iteratedDMB_succ, Fin.init_snoc, Fin.snoc_last]
  exact ((hf.of_le hk).contDiffMBOn_iteratedDMB_slice hU v).dMB_add hU hx a b

theorem ContDiffMBOn.iteratedDMB_snoc_smul {m k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffMBOn m f U) (hk : k + 1 ≤ m) {x : E} (hx : x ∈ U)
    (v : Fin k → E) (c : ℝ) (a : E) :
    iteratedDMB (k + 1) f (x, Fin.snoc v (c • a)) =
      c • iteratedDMB (k + 1) f (x, Fin.snoc v a) := by
  simp only [iteratedDMB_succ, Fin.init_snoc, Fin.snoc_last]
  exact ((hf.of_le hk).contDiffMBOn_iteratedDMB_slice hU v).dMB_smul hx c a

/-- Proposition 1.3.17: for `f` of class `C^k` and `x ∈ U`, `d^(k) f (x, ·)` is a continuous
symmetric `k`-linear map. -/
theorem ContDiffMBOn.exists_iteratedDMB_multilinear {k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffMBOn k f U) {x : E} (hx : x ∈ U) :
    ∃ M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F,
      (∀ v, M v = iteratedDMB k f (x, v)) ∧ ∀ (σ : Equiv.Perm (Fin k)) v, M (v ∘ σ) = M v := by
  have hcont : Continuous fun v : Fin k → E ↦ iteratedDMB k f (x, v) :=
    (hf.hasContIterDerivOn.2 k le_rfl).comp_continuous (by fun_prop) fun v ↦ ⟨hx, mem_univ v⟩
  cases k with
  | zero =>
    refine ⟨ContinuousMultilinearMap.constOfIsEmpty ℝ _ (f x), fun v ↦ rfl, fun _ _ ↦ rfl⟩
  | succ k =>
    have key : ∀ (v : Fin (k + 1) → E) (i : Fin (k + 1)) (d : E),
        iteratedDMB (k + 1) f (x, update v i d) =
          iteratedDMB (k + 1) f (x, Fin.snoc (Fin.init (v ∘ Equiv.swap i (Fin.last k))) d) := by
      intro v i d
      rw [← hf.iteratedDMB_perm hU le_rfl hx _ (Equiv.swap i (Fin.last k))]
      congr 2
      rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left]
      conv_lhs => rw [← Fin.snoc_init_self (v ∘ Equiv.swap i (Fin.last k))]
      rw [Fin.update_snoc_last]
    refine ⟨{ toFun := fun v ↦ iteratedDMB (k + 1) f (x, v)
              map_update_add' := ?_
              map_update_smul' := ?_
              cont := hcont }, fun v ↦ rfl, fun σ v ↦ hf.iteratedDMB_perm hU le_rfl hx v σ⟩
    · intro inst v i a b
      obtain rfl : inst = instDecidableEqFin (k + 1) := Subsingleton.elim _ _
      simp only [key]
      exact hf.iteratedDMB_snoc_add hU le_rfl hx _ a b
    · intro inst v i c a
      obtain rfl : inst = instDecidableEqFin (k + 1) := Subsingleton.elim _ _
      simp only [key]
      exact hf.iteratedDMB_snoc_smul hU le_rfl hx _ c a

end LocallyConvex

end LCAnalysis
