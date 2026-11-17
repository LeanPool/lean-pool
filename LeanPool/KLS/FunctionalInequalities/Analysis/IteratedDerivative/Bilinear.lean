/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.Symmetry
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Raw Leibniz expansion of a bilinear image of two `C^∞` maps

Generic calculus support for the spatial drift algebra of Bizeul–Klartag–Lehec arXiv:2610.05474v1,
p. 21, (72)–(74): for a continuous bilinear `B : F →L[ℝ] G →L[ℝ] H` and globally `C^∞` maps `f, g`
on a real normed space, the `m`-th raw iterated derivative of `y ↦ B (f y) (g y)` is the sum over
all Boolean subset indicators `q : Fin m → Bool` of `B (D^{|q|} f [h_q]) (D^{m−|q|} g [h_{¬q}])`,
each
allocation with coefficient `1` and slots kept in their inherited increasing order (`selected`); no
factorial, Taylor normalisation or symmetry is involved.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Select a subset of the original ordered slots using its Boolean indicator. -/
def selected : {m : ℕ} → (Fin m → E) → (Fin m → Bool) → List E
  | 0, _, _ => []
  | _m + 1, h, q =>
    if q 0 then h 0 :: selected (Fin.tail h) (Fin.tail q)
    else selected (Fin.tail h) (Fin.tail q)

omit [NormedSpace ℝ H] in
private theorem sum_masks_succ {m : ℕ} (Φ : (Fin (m + 1) → Bool) → H) :
    (∑ q, Φ q) =
      (∑ q : Fin m → Bool, Φ (Fin.cons false q)) + ∑ q : Fin m → Bool, Φ (Fin.cons true q) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hb : (Finset.univ : Finset Bool) = { false, true } := by
    ext q
    cases q <;> simp
  rw [hb]
  simp [Fin.consEquiv]

private theorem directional_bilinear_one (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v x : E) :
    fderiv ℝ (fun y => B (f y) (g y)) x v =
      B (f x) (fderiv ℝ g x v) + B (fderiv ℝ f x v) (g x) := by
  rw [B.fderiv_of_bilinear (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

/-- Exact raw higher Leibniz rule for an arbitrary continuous bilinear map.
Each Boolean indicator chooses the derivatives falling on the first factor. -/
theorem directional_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) (fun y => B (f y) (g y)) x =
      ∑ q : Fin m → Bool,
        B (directional (selected h q) f x)
          (directional (selected h (fun i => !(q i))) g x) := by
  induction m generalizing x with
  | zero => simp [directional, selected]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) (fun y => B (f y) (g y))) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) (fun y => B (f y) (g y)) =
        fun y => ∑ q : Fin m → Bool,
          B (directional (selected (Fin.tail h) q) f y)
            (directional (selected (Fin.tail h) (fun i => !(q i))) g y) :=
      funext (fun y => IH (Fin.tail h) y)
    rw [he]
    have hCD (q : Fin m → Bool) : ContDiff ℝ ∞ (fun y =>
        B (directional (selected (Fin.tail h) q) f y)
          (directional (selected (Fin.tail h) (fun i => !(q i))) g y)) :=
      B.isBoundedBilinearMap.contDiff.comp
        ((directional_contDiff hf _).prodMk (directional_contDiff hg _))
    rw [fderiv_fun_sum (fun q _ => (hCD q).differentiable (by simp) x)]
    simp only [sum_apply]
    rw [sum_masks_succ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    rw [directional_bilinear_one B (directional_contDiff hf _) (directional_contDiff hg _)]
    simp only [selected, Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, Fin.tail_cons,
      Bool.not_false, Bool.not_true, directional]
    rfl

/-- Exact raw iterated Fréchet Leibniz expansion, retaining every subset allocation. -/
theorem iteratedFDeriv_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (h : Fin m → E) (x : E) :
    iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x h =
      ∑ q : Fin m → Bool,
        B (directional (selected h q) f x)
          (directional (selected h (fun i => !(q i))) g x) := by
  have hB : ContDiff ℝ ∞ (fun y => B (f y) (g y)) := by
    simpa only [Function.comp_def] using B.isBoundedBilinearMap.contDiff.comp (hf.prodMk hg)
  rw [← directional_ofFn hB]
  exact directional_bilinear B hf hg m h x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The mask selector returns the empty list exactly for the all-`false` mask. -/
theorem selected_eq_nil_iff {m : ℕ} (h : Fin m → E) (q : Fin m → Bool) :
    selected h q = [] ↔ ∀ i, q i = false := by
    induction m with
    | zero =>
        simp [selected]
    | succ m ih =>
        cases hq0 : q 0 with
        | false =>
            simp [selected, hq0, ih (Fin.tail h) (Fin.tail q),
              Fin.forall_fin_succ, Fin.tail]
        | true =>
            simp [selected, hq0, Fin.forall_fin_succ]

/--
Complement pairing of Boolean masks: if a predicate and a real summand are invariant under
complementing the mask, the
filtered sum is twice the sum over the masks selecting a fixed slot `i₀` (BKL (74): pairs `J`, `Jᶜ`,
representative containing
slot `i₀`). -/
theorem sum_filter_eq_two_mul_sum_filter_of_compl_invariant {m : ℕ} (P : (Fin m → Bool) → Prop)
    [DecidablePred P] (hP : ∀ q, P (fun i => !(q i)) ↔ P q) (f : (Fin m → Bool) → ℝ)
    (hf : ∀ q, f (fun i => !(q i)) = f q) (i₀ : Fin m) :
    ∑ q ∈ Finset.univ.filter P, f q =
      2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by
  let c : (Fin m → Bool) → (Fin m → Bool) := fun q i => !(q i)
  have hcc (q : Fin m → Bool) : c (c q) = q := by
    funext i
    simp [c]
  have hsum :
    (∑ q ∈ Finset.univ.filter (fun q => q i₀ = false ∧ P q), f q) =
      ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by
    refine Finset.sum_bij (fun q _ => c q) ?_ ?_ ?_ ?_
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [c] using hq'.2.1
      · simpa [c] using (hP q).mpr hq'.2.2
    · intro q₁ hq₁ q₂ hq₂ h
      calc
        q₁ = c (c q₁) := (hcc q₁).symm
        _ = c (c q₂) := congrArg c h
        _ = q₂ := hcc q₂
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      refine ⟨c q, ?_, hcc q⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [c] using hq'.2.1
      · simpa [c] using (hP q).mpr hq'.2.2
    · intro q hq
      simpa [c] using (hf q).symm
  have hsplit :
    (∑ q ∈ Finset.univ.filter P, f q) =
      (∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q) +
        ∑ q ∈ Finset.univ.filter (fun q => q i₀ = false ∧ P q), f q := by
    simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ.filter P) (p := fun q =>
          q i₀ = true) (f := f)).symm
  calc
    (∑ q ∈ Finset.univ.filter P, f q) =
        (∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q) +
          ∑ q ∈ Finset.univ.filter (fun q => q i₀ = false ∧ P q), f q :=
      hsplit
    _ = 2 * ∑ q ∈ Finset.univ.filter (fun q => q i₀ = true ∧ P q), f q := by
      rw [hsum]
      ring

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

/--
Boolean-mask partition facts for the actual ordered `selected` lists (BKL arXiv:2610.05474v1,
(72)–(74),
singleton and middle allocations): lengths add up to `m`, the two selections together are a
permutation of the
slots, an indicator of one slot selects exactly that slot, and a selection of length `1` comes from
such an
indicator. Repeated slot values and `m = 0` are included.
-/
theorem selected_mask_partition {E : Type*} {m : ℕ} (h : Fin m → E) (q : Fin m → Bool) :
    (selected h q).length + (selected h (fun i => !(q i))).length = m ∧
      (selected h q ++ selected h (fun i => !(q i))).Perm (List.ofFn h) ∧
        (∀ i : Fin m, selected h (fun j => decide (j = i)) = [h i]) ∧
          ((selected h q).length = 1 → ∃ i : Fin m, q = fun j => decide (j = i)) := by
  induction m with
  | zero => simp [selected]
  | succ m ih =>
    obtain ⟨hlen, hperm, hsingle, hone⟩ := ih (Fin.tail h) (Fin.tail q)
    have hnot : Fin.tail (fun i : Fin (m + 1) => !(q i)) = (fun i : Fin m => !(Fin.tail q i)) := by
      funext i
      rfl
    have htailh : List.ofFn (Fin.tail h) = List.ofFn (fun i : Fin m => h i.succ) := by
      apply congrArg (fun f : Fin m → E => List.ofFn f)
      funext i
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases hq0 : q 0 with
      | false =>
        simp [selected, hq0, hnot] at hlen ⊢
        omega
      | true =>
        simp [selected, hq0, hnot] at hlen ⊢
        omega
    · cases hq0 : q 0 with
      |
        false =>
        have move (l r : List E) (a : E) : (l ++ a :: r).Perm (a :: (l ++ r)) := by
          induction l with
          | nil => exact List.Perm.refl _
          | cons b l ihl => exact (List.Perm.cons b ihl).trans (List.Perm.swap _ _ _)
        have hp :=
          (move (selected (Fin.tail h) (Fin.tail q))
                (selected (Fin.tail h) (fun i => !(Fin.tail q i))) (h 0)).trans
            (hperm.cons (h 0))
        rw [htailh] at hp
        simpa [selected, hq0, hnot, List.ofFn_succ] using hp
      | true =>
        have hp := hperm.cons (h 0)
        rw [htailh] at hp
        simpa [selected, hq0, hnot, List.ofFn_succ] using hp
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · have hnil :
          selected (Fin.tail h)
              (Fin.tail (fun j : Fin (m + 1) => decide (j = (0 : Fin (m + 1))))) =
            [] := by
          apply
            (selected_eq_nil_iff (Fin.tail h)
                (Fin.tail (fun j : Fin (m + 1) => decide (j = (0 : Fin (m + 1)))))).2
          intro j
          have hn : (j.succ : Fin (m + 1)) ≠ 0 := Fin.succ_ne_zero j
          change decide (j.succ = (0 : Fin (m + 1))) = false
          simp [hn]
        simp [selected, hnil]
      · have hzero : (fun j : Fin (m + 1) => decide (j = k.succ)) 0 = false := by
          have hn : (0 : Fin (m + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
          simp [hn]
        have hmask :
          Fin.tail (fun j : Fin (m + 1) => decide (j = k.succ)) =
            (fun j : Fin m => decide (j = k)) := by
          funext j
          simp only [Fin.tail, Fin.succ_inj]
        have hs := hsingle k
        change selected (Fin.tail h) (fun j => decide (j = k)) = [h k.succ] at hs
        simpa [selected, hzero, hmask] using hs
    · intro hlength
      cases hq0 : q 0 with
      |
        false =>
        have ht : (selected (Fin.tail h) (Fin.tail q)).length = 1 := by
          simpa [selected, hq0] using hlength
        obtain ⟨i, hi⟩ := hone ht
        have hn : (0 : Fin (m + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
        refine ⟨i.succ, ?_⟩
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [hq0, hn]
        · have hk : q k.succ = decide (k = i) := by simpa [Fin.tail] using congrFun hi k
          simpa only [Fin.succ_inj] using hk
      |
        true =>
        have ht : (selected (Fin.tail h) (Fin.tail q)).length = 0 := by
          simpa [selected, hq0] using hlength
        have hall :=
          (selected_eq_nil_iff (Fin.tail h) (Fin.tail q)).mp (List.length_eq_zero_iff.mp ht)
        refine ⟨0, ?_⟩
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [hq0]
        · have hk : q k.succ = false := by simpa [Fin.tail] using hall k
          have hs : (k.succ : Fin (m + 1)) ≠ 0 := Fin.succ_ne_zero k
          simp [hk, hs]

end FunctionalInequalities.Analysis
