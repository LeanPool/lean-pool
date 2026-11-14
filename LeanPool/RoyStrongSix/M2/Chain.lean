/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import LeanPool.RoyStrongSix.M2.Torus

/-!
# Roy's chain of ideals (Roy §8.4.1)

* `DwL l Q`: the derivations `D_w` along a list `l` (first element applied first).
* `VO W n J`: the ideal of `x` with `D_l x ∈ J` for every list `l ⊆ W` with `|l| ≤ n` ("vanishing to
  order `> n` along `W` modulo `J`"). It is an ideal by Leibniz (`VO_mul`), so Roy's vanishing claim
  can be checked on generators.
* `sig S r = Σ[r]`, `gensR`, `Lr r = I_G + (τ_σ D_l P : σ ∈ Σ[r], |l| ≤ rS₀)`: an increasing chain.
* `hdim_L0_lt`: `hdim L₀ < d₀ + d₁`, since `I(G)` is prime (`vanish_univ_isPrime`).
* **`exists_flat`** (pigeonhole): some `r < d₀ + d₁` has `hdim L_r = hdim L_{r+1}`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

/-! ### Iterated invariant derivations -/

/-- `D_{w_r} ⋯ D_{w_1} Q` for `l = [w₁, …, w_r]`. -/
noncomputable def DwL (l : List (LieG K d0 d1)) (Q : B) : B := l.foldl (fun Q w => Dw w Q) Q

@[simp] theorem DwL_nil (Q : B) : DwL [] Q = Q := rfl

theorem DwL_cons (w : LieG K d0 d1) (l : List (LieG K d0 d1)) (Q : B) :
    DwL (w :: l) Q = DwL l (Dw w Q) := rfl

theorem DwL_append (l l' : List (LieG K d0 d1)) (Q : B) : DwL (l ++ l') Q = DwL l' (DwL l Q) :=
  List.foldl_append ..

theorem DwL_add (l : List (LieG K d0 d1)) (Q Q' : B) : DwL l (Q + Q') = DwL l Q + DwL l Q' := by
  induction l generalizing Q Q' with
  | nil => rfl
  | cons w l ih => rw [DwL_cons, DwL_cons, DwL_cons, map_add, ih]

theorem DwL_zero (l : List (LieG K d0 d1)) : DwL l (0 : B) = 0 := by
  induction l with
  | nil => rfl
  | cons w l ih => rw [DwL_cons, map_zero, ih]

theorem DwL_transl (l : List (LieG K d0 d1)) (g : GPt K d0 d1) (Q : B) :
    DwL l (transl g Q) = transl g (DwL l Q) := by
  induction l generalizing Q with
  | nil => rfl
  | cons w l ih => rw [DwL_cons, DwL_cons, Dw_transl, ih]

theorem DwL_IG (l : List (LieG K d0 d1)) {Q : B} (hQ : Q ∈ (IG : Ideal B)) : DwL l Q ∈ (IG :
  Ideal B) := by
  induction l generalizing Q with
  | nil => exact hQ
  | cons w l ih => exact ih (Dw_IG w hQ)

theorem DwL_mem_FLE (l : List (LieG K d0 d1)) {D : Fin 2 → ℕ} {Q : B} (hQ : Q ∈ FLE K blk D) :
    DwL l Q ∈ FLE K blk D := by
  induction l generalizing Q with
  | nil => exact hQ
  | cons w l ih => exact ih (Dw_mem_FLE w hQ)

theorem DL_eq_DwL {ℓ : ℕ} (w : Fin ℓ → LieG K d0 d1) (l : List (Fin ℓ)) (x : B) :
    DL (fun i => Dw (w i)) l x = DwL (l.map w) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => rw [DL_cons, ih, List.map_cons, DwL_cons]

/-! ### Vanishing to order `> n` -/

theorem VO_mul (W : Submodule K (LieG K d0 d1)) (J : Ideal B) :
    ∀ (n : ℕ) (a x : B), (∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) → l.length ≤ n → DwL l x ∈
      J) →
      ∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) → l.length ≤ n → DwL l (a * x) ∈ J := by
  intro n
  induction n with
  | zero =>
    intro a x hx l _ hl
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
    exact J.mul_mem_left a (hx [] (by simp) le_rfl)
  | succ n ih =>
    intro a x hx l hlW hl
    cases l with
    | nil => exact J.mul_mem_left a (hx [] (by simp) (Nat.zero_le _))
    | cons w l =>
      have hw : w ∈ W := hlW w List.mem_cons_self
      have hlW' : ∀ w ∈ l, w ∈ W := fun v hv => hlW v (List.mem_cons_of_mem _ hv)
      have hl' : l.length ≤ n := by simpa using hl
      rw [DwL_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, DwL_add]
      refine J.add_mem (ih a (Dw w x) (fun l' hl'W hl'n => ?_) l hlW' hl')
        (by
          rw [mul_comm]
          exact ih (Dw w a) x (fun l' hl'W hl'n => hx l' hl'W (by omega)) l hlW' hl')
      rw [← DwL_cons]
      exact hx _ (fun v hv => (List.mem_cons.mp hv).elim (· ▸ hw) (hl'W v))
        (by simp only [List.length_cons]; omega)

/-- Elements vanishing to order `> n` along `W` modulo `J`. -/
def VO (W : Submodule K (LieG K d0 d1)) (n : ℕ) (J : Ideal B) : Ideal B where
  carrier := {x | ∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) → l.length ≤ n → DwL l x ∈ J}
  add_mem' hx hy l hlW hl := by rw [DwL_add]; exact J.add_mem (hx l hlW hl) (hy l hlW hl)
  zero_mem' l _ _ := by rw [DwL_zero]; exact J.zero_mem
  smul_mem' a x hx := VO_mul W J n a x hx

theorem VO_le (W : Submodule K (LieG K d0 d1)) (n : ℕ) (J : Ideal B) : VO W n J ≤ J :=
  fun x hx => hx [] (by simp) (Nat.zero_le _)

theorem VO_mono (W : Submodule K (LieG K d0 d1)) (n : ℕ) {J J' : Ideal B} (h : J ≤ J') :
    VO W n J ≤ VO W n J' := fun _ hx l hlW hl => h (hx l hlW hl)

theorem IG_le_VO (W : Submodule K (LieG K d0 d1)) (n : ℕ) (E : Set (GPt K d0 d1)) :
    (IG : Ideal B) ≤ VO W n (vanish E) :=
  fun _ hx l _ _ => IG_le_vanish' E (DwL_IG l hx)

/-! ### The sets `Σ[r]` -/

/-- `Σ[r] = {σ₁ + ⋯ + σ_r : σᵢ ∈ S}`. -/
def sig (S : Finset (GPt K d0 d1)) (r : ℕ) : Set (GPt K d0 d1) :=
  {g | ∃ σ : Fin r → GPt K d0 d1, (∀ i, σ i ∈ S) ∧ g = gsum σ}

theorem gsum_snoc {r : ℕ} (σ : Fin r → GPt K d0 d1) (s : GPt K d0 d1) :
    gsum (Fin.snoc σ s : Fin (r + 1) → GPt K d0 d1) = gmul (gsum σ) s := by
  simp only [gsum, gmul, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last]

theorem zero_mem_sig (S : Finset (GPt K d0 d1)) : GPt.zero ∈ sig S 0 :=
  ⟨Fin.elim0, fun i => i.elim0, by simp [gsum, GPt.zero]⟩

theorem gmul_mem_sig {S : Finset (GPt K d0 d1)} {r : ℕ} {g s : GPt K d0 d1} (hg : g ∈ sig S r)
    (hs : s ∈ S) : gmul g s ∈ sig S (r + 1) := by
  obtain ⟨σ, hσ, rfl⟩ := hg
  refine ⟨Fin.snoc σ s, fun i => ?_, (gsum_snoc σ s).symm⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa using hs
  · simpa using hσ i

theorem gmul_zero (g : GPt K d0 d1) : gmul g GPt.zero = g := by
  simp [gmul, GPt.zero]

theorem sig_mono {S : Finset (GPt K d0 d1)} (hS : GPt.zero ∈ S) (r : ℕ) : sig S r ⊆ sig S (r + 1) :=
  fun g hg => by simpa [gmul_zero] using gmul_mem_sig hg hS

/-! ### The chain -/

variable (W : Submodule K (LieG K d0 d1)) (S : Finset (GPt K d0 d1))
  (Pt : MvPolynomial (V3 d0 d1) K) (S0 : ℕ)

/-- Generators of `L_r`: `τ_σ D_l P` with `σ ∈ Σ[r]`, `l ⊆ W`, `|l| ≤ r S₀`. -/
def gensR (r : ℕ) : Set B :=
  {Q | ∃ σ ∈ sig S r, ∃ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) ∧ l.length ≤ r * S0 ∧
    Q = transl σ (DwL l Pt)}

/-- Roy's ideal `I_{r+1}`. -/
noncomputable def Lr (r : ℕ) : Ideal B := IG ⊔ Ideal.span (gensR W S Pt S0 r)

theorem gensR_mono (hS : GPt.zero ∈ S) (r : ℕ) : gensR W S Pt S0 r ⊆ gensR W S Pt S0 (r + 1) := by
  rintro _ ⟨σ, hσ, l, hlW, hl, rfl⟩
  exact ⟨σ, sig_mono hS r hσ, l, hlW, by nlinarith, rfl⟩

theorem Lr_mono (hS : GPt.zero ∈ S) (r : ℕ) : Lr W S Pt S0 r ≤ Lr W S Pt S0 (r + 1) :=
  sup_le_sup_left (Ideal.span_mono (gensR_mono W S Pt S0 hS r)) _

theorem Pt_mem_L0 : Pt ∈ Lr W S Pt S0 0 := by
  refine Ideal.mem_sup_right (Ideal.subset_span ⟨GPt.zero, zero_mem_sig S, [], by simp, by simp,
    ?_⟩)
  rw [DwL_nil, transl_zero]

theorem gensR_mem_FLE {D : Fin 2 → ℕ} (hPD : Pt ∈ FLE K blk D) (r : ℕ) :
    ∀ Q ∈ gensR W S Pt S0 r, Q ∈ FLE K blk D := by
  rintro _ ⟨σ, _, l, _, _, rfl⟩
  exact transl_mem_FLE D σ (DwL_mem_FLE l hPD)

/-- The last ideal is proper: everything vanishes at `e`. -/
theorem Lr_le_vanish_zero {r : ℕ}
    (hvan : ∀ g ∈ sig S r, ∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) → l.length ≤ r * S0 →
      eval (pt g) (DwL l Pt) = 0) :
    Lr W S Pt S0 r ≤ vanish {GPt.zero} := by
  refine sup_le (IG_le_vanish' _) (Ideal.span_le.mpr ?_)
  rintro _ ⟨σ, hσ, l, hlW, hl, rfl⟩ g hg
  rw [Set.mem_singleton_iff.mp hg, eval_transl, gmul_zero]
  exact hvan σ hσ l hlW hl

theorem Lr_mono' (hS : GPt.zero ∈ S) {r r' : ℕ} (h : r ≤ r') : Lr W S Pt S0 r ≤ Lr W S Pt S0 r'
  := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (Lr_mono W S Pt S0 hS n)

variable [CharZero K] (D : Fin 2 → ℕ)

/-- `hdim L₀ < d₀ + d₁`. -/
theorem hdim_L0_lt [IsAlgClosed K] (hD : ∀ i, 1 ≤ D i) {D0 D1 : ℕ} (hDD : D = ![D0, D1])
    (hPt : Pt ∉ vanish (Set.univ : Set (GPt K d0 d1))) (hL0 : Lr W S Pt S0 0 ≠ ⊤) :
    (hdata blk D K (Lr W S Pt S0 0)).1 < d0 + d1 := by
  set L := Lr W S Pt S0 0
  have hIGL : (IG : Ideal B) ≤ L := le_sup_left
  have hrad : L.radical ≠ ⊤ := fun h => hL0 (Ideal.radical_eq_top.mp h)
  -- `I(G) = √I_G`
  have hIGrad : vanish (Set.univ : Set (GPt K d0 d1)) = (IG : Ideal B).radical := by
    rw [← vanish_zeros_eq le_rfl]
    congr 1
    exact (Set.eq_univ_of_forall fun g P hP => IG_le_vanish hP g (Set.mem_univ g)).symm
  have hle : vanish (Set.univ : Set (GPt K d0 d1)) ⊔ Ideal.span {Pt} ≤ L.radical := by
    refine sup_le ?_ ?_
    · rw [hIGrad]; exact Ideal.radical_mono hIGL
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.le_radical (Pt_mem_L0 W S Pt S0)
  have := vanish_univ_isPrime (K := K) (d0 := d0) (d1 := d1)
  have hlt := hdim_section_lt blk D K hD (J := vanish Set.univ) (P := Pt)
    (fun Q hQ => (Ideal.IsPrime.mem_or_mem inferInstance hQ).resolve_left hPt) hle hrad
  rw [hdim_radical blk D hD hL0] at hlt
  have hIGne : (IG : Ideal B) ≠ ⊤ := ne_top_of_le_ne_top hL0 hIGL
  rw [hIGrad, hdim_radical blk D hD hIGne] at hlt
  subst hDD
  have hD0 : 1 ≤ D0 := by simpa using hD 0
  have hD1 : 1 ≤ D1 := by simpa using hD 1
  rw [(hdata_IG (K := K) (d0 := d0) (d1 := d1) hD0 hD1).2.1] at hlt
  exact hlt

/-- **Pigeonhole**: two consecutive ideals of the chain have the same Hilbert dimension. -/
theorem exists_flat [IsAlgClosed K] (hD : ∀ i, 1 ≤ D i) {D0 D1 : ℕ} (hDD : D = ![D0, D1])
    (hS : GPt.zero ∈ S) (hPt : Pt ∉ vanish (Set.univ : Set (GPt K d0 d1)))
    (hlast : Lr W S Pt S0 (d0 + d1) ≠ ⊤) :
    ∃ r < d0 + d1, (hdata blk D K (Lr W S Pt S0 (r + 1))).1 = (hdata blk D K (Lr W S Pt S0 r)).1
      := by
  have hne : ∀ r ≤ d0 + d1, Lr W S Pt S0 r ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hlast (Lr_mono' W S Pt S0 hS hr)
  by_contra hcon
  push Not at hcon
  have hstep : ∀ r < d0 + d1,
      (hdata blk D K (Lr W S Pt S0 (r + 1))).1 < (hdata blk D K (Lr W S Pt S0 r)).1 := by
    intro r hr
    rcases hdata_le_of_le blk D K (Lr_mono W S Pt S0 hS r) (hne (r + 1) (by omega)) with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hcon r hr)
  have hdec : ∀ r ≤ d0 + d1,
      (hdata blk D K (Lr W S Pt S0 r)).1 + r ≤ (hdata blk D K (Lr W S Pt S0 0)).1 := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have := hstep r (by omega)
      have := ih (by omega)
      omega
  have h0 := hdim_L0_lt W S Pt S0 D hD hDD hPt (hne 0 (Nat.zero_le _))
  have := hdec (d0 + d1) le_rfl
  omega

end StrongSix.M2

end LeanPool
