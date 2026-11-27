/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.CommRing

/-!
# Theorem T2: Strictly Bilinear 2-Access Frobenius Collapse over Characteristic 2

Over any commutative ring `R` of characteristic 2 (in particular `F_2[x, c_0, ..., c_k]`,
`F_{2^m}`, or any commutative `F_2`-algebra), we prove that for every `k ≥ 1`, there exists
an explicit passive-output register program using ONLY strictly bilinear basic instructions
(`R_i ← R_i + R_j * R_l` with `j ≠ i, l ≠ i`) and input additions (`R_i ← R_i + x`) that
cleanly computes `R_0 ← R_0 + x^(2^k)` using:
  * `k + 1` registers,
  * `4 * k - 2` bilinear instructions,
  * **EXACTLY 2 input accesses to `x`**!

This shows that the characteristic-2 collapse of Vinciguerra's 4-access lower bound
(`arXiv:2609.18692`, Theorems 3.2–3.3) persists even under the strictest bilinear
instruction restriction. Moreover, **Theorem T2b** (`frobDistinctProg`) eliminates all
self-squares `R_a * R_a` using one swap catalyst (`k + 2` registers, strictly pairwise-distinct
bilinear operands plus passive linear copies) while keeping exact cleanliness and 2 accesses.
-/

namespace Catalytic

universe u

/-- Strictly bilinear register instruction on `n` registers (`0` is the output register). -/
public inductive BilinInstr (n : Nat) where
  /-- `R_dst ← R_dst + R_a * R_b` (bilinear basic instruction; zero input accesses). -/
  | mulAdd (dst a b : Fin n) : BilinInstr n
  /-- `R_dst ← R_dst + x` (single input access). -/
  | addInput (dst : Fin n) : BilinInstr n
  deriving DecidableEq, Repr

/-- Number of input accesses in a bilinear register program. -/
public def BilinProg.accesses {n : Nat} : List (BilinInstr n) → Nat
  | [] => 0
  | .mulAdd _ _ _ :: rest => BilinProg.accesses rest
  | .addInput _ :: rest => 1 + BilinProg.accesses rest

/-- Number of bilinear basic instructions in a program. -/
public def BilinProg.bilinOps {n : Nat} : List (BilinInstr n) → Nat
  | [] => 0
  | .mulAdd _ _ _ :: rest => 1 + BilinProg.bilinOps rest
  | .addInput _ :: rest => BilinProg.bilinOps rest

/-- Passive-output and non-self-referential validity check (`dst ≠ a`, `dst ≠ b`, and register `0` is never read). -/
public def BilinInstr.isValidPassive {n : Nat} : BilinInstr n → Prop
  | .mulAdd dst a b => dst ≠ a ∧ dst ≠ b ∧ a.val ≠ 0 ∧ b.val ≠ 0
  | .addInput _ => True

/-- Strictly distinct-operand validity: additionally forbids `a = b` (no self-squaring). -/
public def BilinInstr.isStrictDistinctPassive {n : Nat} : BilinInstr n → Prop
  | .mulAdd dst a b => dst ≠ a ∧ dst ≠ b ∧ a ≠ b ∧ a.val ≠ 0 ∧ b.val ≠ 0
  | .addInput _ => True

/-- Execute one bilinear instruction over any commutative ring `R`. -/
public def BilinInstr.exec {n : Nat} {R : Type u} [CRing R]
    (x : R) (st : Fin n → R) : BilinInstr n → (Fin n → R)
  | .mulAdd dst a b => fun i => if i = dst then st dst + st a * st b else st i
  | .addInput dst => fun i => if i = dst then st dst + x else st i

/-- Execute a list of bilinear instructions left-to-right. -/
public def BilinProg.exec {n : Nat} {R : Type u} [CRing R]
    (x : R) : List (BilinInstr n) → (Fin n → R) → (Fin n → R)
  | [], st => st
  | instr :: rest, st => BilinProg.exec x rest (instr.exec x st)

theorem BilinProg.exec_append {n : Nat} {R : Type u} [CRing R]
    (x : R) (p q : List (BilinInstr n)) (st : Fin n → R) :
    BilinProg.exec x (p ++ q) st = BilinProg.exec x q (BilinProg.exec x p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih => exact ih (i.exec x st)

theorem BilinProg.accesses_append {n : Nat} (p q : List (BilinInstr n)) :
    BilinProg.accesses (p ++ q) = BilinProg.accesses p + BilinProg.accesses q := by
  induction p with
  | nil => simp [BilinProg.accesses]
  | cons i rest ih =>
    cases i <;> simp [BilinProg.accesses, ih, Nat.add_assoc]

theorem BilinProg.bilinOps_append {n : Nat} (p q : List (BilinInstr n)) :
    BilinProg.bilinOps (p ++ q) = BilinProg.bilinOps p + BilinProg.bilinOps q := by
  induction p with
  | nil => simp [BilinProg.bilinOps]
  | cons i rest ih =>
    cases i <;> simp [BilinProg.bilinOps, ih, Nat.add_assoc]

/-- Forward squaring cascade: for `j = 1, ..., m`, execute `R_{j+1} ← R_{j+1} + R_j * R_j`. -/
public def sqCascadeFwd (n : Nat) : (m : Nat) → (hm : m + 1 < n) → List (BilinInstr n)
  | 0, _ => []
  | m + 1, hm =>
    sqCascadeFwd n m (by omega) ++
      [.mulAdd ⟨m + 2, hm⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩]

/-- Backward squaring cascade (exact reverse of `sqCascadeFwd`). -/
public def sqCascadeBwd (n : Nat) : (m : Nat) → (hm : m + 1 < n) → List (BilinInstr n)
  | 0, _ => []
  | m + 1, hm =>
    .mulAdd ⟨m + 2, hm⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩ ::
      sqCascadeBwd n m (by omega)

/-- The 2-access passive-output bilinear Frobenius program for `x^(2^k)` on `k + 1` registers (`k ≥ 1`). -/
public def frobBilinProg (k : Nat) (hk : 1 ≤ k) : List (BilinInstr (k + 1)) :=
  let r0 : Fin (k + 1) := ⟨0, by omega⟩
  let r1 : Fin (k + 1) := ⟨1, by omega⟩
  let rk : Fin (k + 1) := ⟨k, by omega⟩
  let fwd := sqCascadeFwd (k + 1) (k - 1) (by omega)
  let bwd := sqCascadeBwd (k + 1) (k - 1) (by omega)
  [.addInput r1] ++ fwd ++ [.mulAdd r0 rk rk] ++ bwd ++
  [.addInput r1] ++ fwd ++ [.mulAdd r0 rk rk] ++ bwd

/-- Closed-form cascaded state after running `sqCascadeFwd n m hm` on state `st` over a `Char2CRing`. -/
def cascadeVal {n : Nat} {R : Type u} [CRing R] (st : Fin n → R) :
    (j : Nat) → (hj : j < n) → R
  | 0, hj => st ⟨0, hj⟩
  | 1, hj => st ⟨1, hj⟩
  | j + 2, hj => st ⟨j + 2, hj⟩ + cascadeVal st (j + 1) (by omega) * cascadeVal st (j + 1) (by omega)

private theorem sqCascadeFwd_accesses (n m : Nat) (hm : m + 1 < n) :
    BilinProg.accesses (sqCascadeFwd n m hm) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [sqCascadeFwd, BilinProg.accesses_append, BilinProg.accesses, ih]

private theorem sqCascadeBwd_accesses (n m : Nat) (hm : m + 1 < n) :
    BilinProg.accesses (sqCascadeBwd n m hm) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [sqCascadeBwd, BilinProg.accesses, ih]

private theorem sqCascadeFwd_bilinOps (n m : Nat) (hm : m + 1 < n) :
    BilinProg.bilinOps (sqCascadeFwd n m hm) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [sqCascadeFwd, BilinProg.bilinOps_append, BilinProg.bilinOps, ih]

private theorem sqCascadeBwd_bilinOps (n m : Nat) (hm : m + 1 < n) :
    BilinProg.bilinOps (sqCascadeBwd n m hm) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [sqCascadeBwd, BilinProg.bilinOps, ih, Nat.add_comm]

private theorem sqCascadeFwd_valid (n m : Nat) (hm : m + 1 < n) :
    ∀ instr ∈ sqCascadeFwd n m hm, instr.isValidPassive := by
  induction m with
  | zero => intro _ h; cases h
  | succ m ih =>
    intro instr h
    simp only [sqCascadeFwd, List.mem_append, List.mem_singleton] at h
    rcases h with h1 | rfl
    · exact ih (by omega) instr h1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro heq; have := congrArg Fin.val heq; simp at this
      · intro heq; have := congrArg Fin.val heq; simp at this
      · simp
      · simp

private theorem sqCascadeBwd_valid (n m : Nat) (hm : m + 1 < n) :
    ∀ instr ∈ sqCascadeBwd n m hm, instr.isValidPassive := by
  induction m with
  | zero => intro _ h; cases h
  | succ m ih =>
    intro instr h
    simp only [sqCascadeBwd, List.mem_cons] at h
    rcases h with rfl | h1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro heq; have := congrArg Fin.val heq; simp at this
      · intro heq; have := congrArg Fin.val heq; simp at this
      · simp
      · simp
    · exact ih (by omega) instr h1

private theorem sqCascadeFwd_exec {n : Nat} {R : Type u} [CRing R]
    (x : R) (m : Nat) (hm : m + 1 < n) (st : Fin n → R) :
    ∀ i : Fin n,
      BilinProg.exec x (sqCascadeFwd n m hm) st i =
        if i.val ≤ m + 1 then cascadeVal st i.val i.isLt else st i := by
  induction m with
  | zero =>
    intro i
    simp only [sqCascadeFwd, BilinProg.exec]
    split
    · rename_i hle
      have hcases : i.val = 0 ∨ i.val = 1 := by omega
      rcases hcases with h0 | h1
      · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
        rw [hi]; simp [cascadeVal]
      · have hi : i = ⟨1, by omega⟩ := Fin.ext h1
        rw [hi]; simp [cascadeVal]
    · rfl
  | succ m ih =>
    intro i
    rw [sqCascadeFwd, BilinProg.exec_append]
    simp only [BilinProg.exec, BilinInstr.exec]
    have hprev := ih (by omega)
    by_cases htop : i = ⟨m + 2, hm⟩
    · subst htop
      have h1 := hprev ⟨m + 2, hm⟩
      have h2 := hprev ⟨m + 1, by omega⟩
      have hnot : ¬ (m + 2 ≤ m + 1) := by omega
      have hle1 : m + 1 ≤ m + 1 := Nat.le_refl _
      have hle2 : m + 2 ≤ m + 2 := Nat.le_refl _
      simp only [↓reduceIte, hnot, hle1, hle2] at h1 h2 ⊢
      rw [h1, h2]
      rfl
    · simp only [htop, ↓reduceIte]
      rw [hprev i]
      have hne : i.val ≠ m + 2 := fun h => htop (Fin.ext h)
      by_cases hle : i.val ≤ m + 1
      · have hle' : i.val ≤ m + 2 := by omega
        simp [hle, hle']
      · have hle' : ¬ (i.val ≤ m + 2) := by omega
        simp [hle, hle']

/-- In a `Char2CRing`, every `mulAdd` is self-inverse! -/
private theorem mulAdd_self_inv {n : Nat} {R : Type u} [Char2CRing R]
    (x : R) (dst a b : Fin n) (hda : dst ≠ a) (hdb : dst ≠ b) (st : Fin n → R) :
    (BilinInstr.mulAdd dst a b).exec x ((BilinInstr.mulAdd dst a b).exec x st) = st := by
  funext i
  simp only [BilinInstr.exec]
  by_cases hi : i = dst
  · rw [hi]
    have hna : a ≠ dst := hda.symm
    have hnb : b ≠ dst := hdb.symm
    simp only [↓reduceIte, hna, hnb]
    rw [CRing.add_assoc, Char2CRing.add_self, CRing.add_zero]
  · simp [hi]

/-- Running `sqCascadeFwd` followed by `sqCascadeBwd` restores the state identically in char 2! -/
private theorem sqCascadeFwd_bwd_cancel {n : Nat} {R : Type u} [Char2CRing R]
    (x : R) (m : Nat) (hm : m + 1 < n) (st : Fin n → R) :
    BilinProg.exec x (sqCascadeBwd n m hm) (BilinProg.exec x (sqCascadeFwd n m hm) st) = st := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sqCascadeFwd, BilinProg.exec_append]
    simp only [sqCascadeBwd, BilinProg.exec]
    have hne : (⟨m + 2, hm⟩ : Fin n) ≠ ⟨m + 1, by omega⟩ := by
      intro h; have := congrArg Fin.val h; simp at this
    rw [mulAdd_self_inv x ⟨m + 2, hm⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩ hne hne]
    exact ih (by omega)

/-- Output update `mulAdd r0 rk rk` commutes with `sqCascadeBwd` because `r0` is never read or written by the cascade! -/
private theorem sqCascadeBwd_comm_r0 {n : Nat} {R : Type u} [CRing R]
    (x : R) (m : Nat) (hm : m + 1 < n) (delta : R) (st : Fin n → R) :
    BilinProg.exec x (sqCascadeBwd n m hm)
      (fun i => if i.val = 0 then st i + delta else st i) =
    (fun i => if i.val = 0 then BilinProg.exec x (sqCascadeBwd n m hm) st i + delta
              else BilinProg.exec x (sqCascadeBwd n m hm) st i) := by
  induction m generalizing st with
  | zero => rfl
  | succ m ih =>
    simp only [sqCascadeBwd, BilinProg.exec]
    have hstep :
        (BilinInstr.mulAdd ⟨m + 2, hm⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩).exec x
          (fun i => if i.val = 0 then st i + delta else st i) =
        (fun i =>
          if i.val = 0 then
            (BilinInstr.mulAdd ⟨m + 2, hm⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩).exec x st i + delta
          else
            (BilinInstr.mulAdd ⟨m + 2, hm⟩ ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩).exec x st i) := by
      funext i
      simp only [BilinInstr.exec]
      by_cases hi0 : i.val = 0
      · have hne : i ≠ ⟨m + 2, hm⟩ := fun h => by
          have hv : i.val = m + 2 := congrArg Fin.val h
          omega
        simp [hi0, hne]
      · simp [hi0]
    rw [hstep]
    exact ih (by omega) _

/-- Key algebraic identity: perturbing register `1` by `+x` shifts `cascadeVal` at index `j ≥ 1` by `+ x^(2^(j-1))`! -/
private theorem cascadeVal_shift_r1 {n : Nat} {R : Type u} [Char2CRing R]
    (st : Fin n → R) (x : R) (j : Nat) (hj1 : 1 ≤ j) (hj : j < n) :
    cascadeVal (fun i => if i = ⟨1, by omega⟩ then st i + x else st i) j hj =
      cascadeVal st j hj + CRing.pow x (2 ^ (j - 1)) := by
  match j with
  | 0 => omega
  | 1 =>
    simp [cascadeVal]
  | m + 2 =>
    simp only [cascadeVal]
    have hne : (⟨m + 2, hj⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h; have hv : m + 2 = 1 := congrArg Fin.val h; omega
    simp only [hne, ↓reduceIte]
    have ih := cascadeVal_shift_r1 st x (m + 1) (by omega) (by omega)
    rw [ih, Char2CRing.add_sq]
    have hsub1 : m + 1 - 1 = m := by omega
    have hsub2 : m + 2 - 1 = m + 1 := by omega
    rw [hsub1, hsub2]
    have hpow : CRing.pow x (2 ^ m) * CRing.pow x (2 ^ m) = CRing.pow x (2 ^ (m + 1)) := by
      rw [← CRing.pow_add]
      have h2 : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by omega
      rw [h2]
    rw [hpow, CRing.add_assoc]

/-- Exact input-access count of `frobBilinProg`: ALWAYS 2, independent of `k`! -/
public theorem frobBilinProg_accesses (k : Nat) (hk : 1 ≤ k) :
    BilinProg.accesses (frobBilinProg k hk) = 2 := by
  simp [frobBilinProg, BilinProg.accesses_append, BilinProg.accesses,
    sqCascadeFwd_accesses, sqCascadeBwd_accesses]

/-- Exact bilinear operation count of `frobBilinProg`: `4 * k - 2` (and `≤ 4 * k`). -/
public theorem frobBilinProg_bilinOps (k : Nat) (hk : 1 ≤ k) :
    BilinProg.bilinOps (frobBilinProg k hk) = 4 * k - 2 := by
  simp [frobBilinProg, BilinProg.bilinOps_append, BilinProg.bilinOps,
    sqCascadeFwd_bilinOps, sqCascadeBwd_bilinOps]
  omega

/-- Every instruction in `frobBilinProg` is passive-output and non-self-referential. -/
public theorem frobBilinProg_valid (k : Nat) (hk : 1 ≤ k) :
    ∀ instr ∈ frobBilinProg k hk, instr.isValidPassive := by
  intro instr h
  simp only [frobBilinProg, List.mem_append, List.mem_singleton] at h
  rcases h with (((((((rfl | h) | rfl) | h) | rfl) | h) | rfl) | h)
  · trivial
  · exact sqCascadeFwd_valid (k + 1) (k - 1) (by omega) instr h
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq; have hv : (0 : Nat) = k := congrArg Fin.val heq; omega
    · intro heq; have hv : (0 : Nat) = k := congrArg Fin.val heq; omega
    · change k ≠ 0; omega
    · change k ≠ 0; omega
  · exact sqCascadeBwd_valid (k + 1) (k - 1) (by omega) instr h
  · trivial
  · exact sqCascadeFwd_valid (k + 1) (k - 1) (by omega) instr h
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq; have hv : (0 : Nat) = k := congrArg Fin.val heq; omega
    · intro heq; have hv : (0 : Nat) = k := congrArg Fin.val heq; omega
    · change k ≠ 0; omega
    · change k ≠ 0; omega
  · exact sqCascadeBwd_valid (k + 1) (k - 1) (by omega) instr h

/--
**Theorem T2 (Strictly Bilinear 2-Access Frobenius Collapse over Characteristic 2).**
For every `k ≥ 1`, every commutative ring `R` of characteristic 2, every `x : R`,
and every arbitrary initial register state `init : Fin (k + 1) → R`:
`frobBilinProg k hk` cleanly computes `init 0 + x^(2^k)` in register `0` and restores
every catalyst register `i ≠ 0` to `init i`, using ONLY **2** input accesses!
-/
public theorem frobBilinProg_clean {R : Type u} [Char2CRing R]
    (k : Nat) (hk : 1 ≤ k) (x : R) (init : Fin (k + 1) → R) :
    let final := BilinProg.exec x (frobBilinProg k hk) init
    final ⟨0, by omega⟩ = init ⟨0, by omega⟩ + CRing.pow x (2 ^ k) ∧
    ∀ i : Fin (k + 1), i.val ≠ 0 → final i = init i := by
  intro final
  let r0 : Fin (k + 1) := ⟨0, by omega⟩
  let r1 : Fin (k + 1) := ⟨1, by omega⟩
  let rk : Fin (k + 1) := ⟨k, by omega⟩
  let fwd := sqCascadeFwd (k + 1) (k - 1) (by omega)
  let bwd := sqCascadeBwd (k + 1) (k - 1) (by omega)
  let st1 : Fin (k + 1) → R := fun i => if i = r1 then init r1 + x else init i
  have hst1 : BilinProg.exec x [.addInput r1] init = st1 := by
    funext i; simp [BilinProg.exec, BilinInstr.exec, st1]
  -- Evaluate phase 1: [addInput r1] ++ fwd ++ [mulAdd r0 rk rk] ++ bwd
  let sf1 := BilinProg.exec x fwd st1
  have hsf1_rk : sf1 rk = cascadeVal st1 k (by omega) := by
    have h := sqCascadeFwd_exec x (k - 1) (by omega) st1 rk
    have hle : k ≤ k - 1 + 1 := by omega
    simpa [sf1, fwd, rk, hle] using h
  let d1 : R := sf1 rk * sf1 rk
  have hmul1 : BilinProg.exec x [.mulAdd r0 rk rk] sf1 =
      (fun i => if i.val = 0 then sf1 i + d1 else sf1 i) := by
    funext i
    simp only [BilinProg.exec, BilinInstr.exec, d1]
    by_cases hi : i.val = 0
    · have hir : i = r0 := Fin.ext hi
      rw [hir]; simp only [r0, ↓reduceIte]
    · have hir : i ≠ r0 := fun h => hi (congrArg Fin.val h)
      simp only [hi, hir, ↓reduceIte]
  have hbwd1 : BilinProg.exec x bwd (BilinProg.exec x [.mulAdd r0 rk rk] sf1) =
      (fun i => if i.val = 0 then st1 i + d1 else st1 i) := by
    rw [hmul1, sqCascadeBwd_comm_r0, sqCascadeFwd_bwd_cancel]
  -- Second input access cancels x from r1!
  let st2 : Fin (k + 1) → R := fun i => if i.val = 0 then init i + d1 else init i
  have hacc2 : BilinProg.exec x [.addInput r1] (fun i => if i.val = 0 then st1 i + d1 else st1 i) = st2 := by
    funext i
    simp only [BilinProg.exec, BilinInstr.exec, st2]
    by_cases hir1 : i = r1
    · rw [hir1]
      have h10 : r1.val ≠ 0 := by simp [r1]
      simp only [h10, ↓reduceIte, st1]
      rw [CRing.add_assoc, Char2CRing.add_self, CRing.add_zero]
    · simp only [hir1, ↓reduceIte, st1]
  -- Evaluate phase 2: fwd ++ [mulAdd r0 rk rk] ++ bwd on st2!
  have hst2_eq : ∀ i : Fin (k + 1), i.val ≠ 0 → st2 i = init i := by
    intro i hi; simp only [st2, hi, ↓reduceIte]
  have hcas2 : ∀ j (hj1 : 1 ≤ j) (hj : j < k + 1), cascadeVal st2 j hj = cascadeVal init j hj := by
    intro j hj1 hj
    induction j with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero =>
        simp only [cascadeVal]
        exact hst2_eq ⟨1, hj⟩ (by simp)
      | succ m' =>
        simp only [cascadeVal]
        rw [hst2_eq ⟨m' + 2, hj⟩ (by simp), ih (by omega) (by omega)]
  let sf2 := BilinProg.exec x fwd st2
  have hsf2_rk : sf2 rk = cascadeVal init k (by omega) := by
    have h := sqCascadeFwd_exec x (k - 1) (by omega) st2 rk
    have hle : k ≤ k - 1 + 1 := by omega
    simp only [sf2, fwd, rk, hle, ↓reduceIte] at h ⊢
    rw [h, hcas2 k hk (by omega)]
  let d2 : R := sf2 rk * sf2 rk
  have hmul2 : BilinProg.exec x [.mulAdd r0 rk rk] sf2 =
      (fun i => if i.val = 0 then sf2 i + d2 else sf2 i) := by
    funext i
    simp only [BilinProg.exec, BilinInstr.exec, d2]
    by_cases hi : i.val = 0
    · have hir : i = r0 := Fin.ext hi
      rw [hir]; simp only [r0, ↓reduceIte]
    · have hir : i ≠ r0 := fun h => hi (congrArg Fin.val h)
      simp only [hi, hir, ↓reduceIte]
  have hbwd2 : BilinProg.exec x bwd (BilinProg.exec x [.mulAdd r0 rk rk] sf2) =
      (fun i => if i.val = 0 then st2 i + d2 else st2 i) := by
    rw [hmul2, sqCascadeBwd_comm_r0, sqCascadeFwd_bwd_cancel]
  -- Assemble full execution trace!
  have hfinal : final = (fun i => if i.val = 0 then st2 i + d2 else st2 i) := by
    change BilinProg.exec x
      ([.addInput r1] ++ fwd ++ [.mulAdd r0 rk rk] ++ bwd ++
       [.addInput r1] ++ fwd ++ [.mulAdd r0 rk rk] ++ bwd) init = _
    simp only [BilinProg.exec_append, hst1]
    change BilinProg.exec x bwd (BilinProg.exec x [.mulAdd r0 rk rk]
      (BilinProg.exec x fwd (BilinProg.exec x [.addInput r1]
        (BilinProg.exec x bwd (BilinProg.exec x [.mulAdd r0 rk rk] sf1))))) = _
    rw [hbwd1, hacc2]
    exact hbwd2
  -- Compute d1 + d2 = x^(2^k)!
  have hshift : sf1 rk = cascadeVal init k (by omega) + CRing.pow x (2 ^ (k - 1)) := by
    rw [hsf1_rk]
    have hst1' : st1 = (fun i => if i = r1 then init i + x else init i) := by
      funext i; by_cases h : i = r1 <;> simp [st1, h]
    rw [hst1']
    exact cascadeVal_shift_r1 init x k hk (by omega)
  have hd_sum : d1 + d2 = CRing.pow x (2 ^ k) := by
    simp only [d1, d2, hshift, hsf2_rk]
    rw [Char2CRing.add_sq]
    have hpow : CRing.pow x (2 ^ (k - 1)) * CRing.pow x (2 ^ (k - 1)) = CRing.pow x (2 ^ k) := by
      rw [← CRing.pow_add]
      have h2 : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
        cases k with
        | zero => omega
        | succ m =>
          have : m + 1 - 1 = m := by omega
          rw [this]; omega
      rw [h2]
    rw [hpow]
    calc
      (cascadeVal init k (by omega) * cascadeVal init k (by omega) + CRing.pow x (2 ^ k)) +
          cascadeVal init k (by omega) * cascadeVal init k (by omega)
          = (cascadeVal init k (by omega) * cascadeVal init k (by omega) +
             cascadeVal init k (by omega) * cascadeVal init k (by omega)) + CRing.pow x (2 ^ k) := by
            rw [CRing.add_assoc, CRing.add_comm (CRing.pow x (2 ^ k)), ← CRing.add_assoc]
      _ = 0 + CRing.pow x (2 ^ k) := by rw [Char2CRing.add_self]
      _ = CRing.pow x (2 ^ k) := CRing.zero_add _
  constructor
  · rw [hfinal]
    simp only [st2, ↓reduceIte]
    rw [CRing.add_assoc, hd_sum]
  · intro i hi
    rw [hfinal]
    simp only [st2, hi, ↓reduceIte]

/-! ## Theorem T2b: Strictly Distinct-Operand 2-Access Frobenius Collapse (`k + 2` registers) -/

/--
Passive-output register instruction disallowing self-squares `R_a * R_a`:
  * `addReg dst src`:    `R_dst ← R_dst + R_src`       (linear copy, `dst ≠ src`, `src ≠ 0`)
  * `mulAdd dst a b`:    `R_dst ← R_dst + R_a * R_b`   (strictly distinct `dst, a, b`, `a ≠ 0, b ≠ 0`)
  * `addInput dst`:      `R_dst ← R_dst + x`           (1 input access)
-/
public inductive DistinctBilinInstr (n : Nat) where
  | addReg (dst src : Fin n) : DistinctBilinInstr n
  | mulAdd (dst a b : Fin n) : DistinctBilinInstr n
  | addInput (dst : Fin n) : DistinctBilinInstr n
  deriving DecidableEq, Repr

/-- Check that the output register is passive and the register operands are distinct. -/
public def DistinctBilinInstr.isStrictValidPassive {n : Nat} : DistinctBilinInstr n → Prop
  | .addReg dst src => dst ≠ src ∧ src.val ≠ 0
  | .mulAdd dst a b => dst ≠ a ∧ dst ≠ b ∧ a ≠ b ∧ a.val ≠ 0 ∧ b.val ≠ 0
  | .addInput _ => True

/-- Count the instructions that read the input. -/
public def DistinctBilinProg.accesses {n : Nat} : List (DistinctBilinInstr n) → Nat
  | [] => 0
  | .addInput _ :: rest => 1 + DistinctBilinProg.accesses rest
  | _ :: rest => DistinctBilinProg.accesses rest

/-- Count register-only instructions, including additions and bilinear updates. -/
public def DistinctBilinProg.basicOps {n : Nat} : List (DistinctBilinInstr n) → Nat
  | [] => 0
  | .addInput _ :: rest => DistinctBilinProg.basicOps rest
  | _ :: rest => 1 + DistinctBilinProg.basicOps rest

/-- Apply one distinct-operand instruction to the register state. -/
public def DistinctBilinInstr.exec {n : Nat} {R : Type u} [CRing R]
    (x : R) (st : Fin n → R) : DistinctBilinInstr n → (Fin n → R)
  | .addReg dst src => fun i => if i = dst then st dst + st src else st i
  | .mulAdd dst a b => fun i => if i = dst then st dst + st a * st b else st i
  | .addInput dst => fun i => if i = dst then st dst + x else st i

/-- Execute the instructions in order starting from the given state. -/
public def DistinctBilinProg.exec {n : Nat} {R : Type u} [CRing R]
    (x : R) : List (DistinctBilinInstr n) → (Fin n → R) → (Fin n → R)
  | [], st => st
  | i :: rest, st => DistinctBilinProg.exec x rest (i.exec x st)

private theorem DistinctBilinProg.exec_append {n : Nat} {R : Type u} [CRing R]
    (x : R) (p q : List (DistinctBilinInstr n)) (st : Fin n → R) :
    DistinctBilinProg.exec x (p ++ q) st = DistinctBilinProg.exec x q (DistinctBilinProg.exec x p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih => exact ih (i.exec x st)

private theorem DistinctBilinProg.accesses_append {n : Nat} (p q : List (DistinctBilinInstr n)) :
    DistinctBilinProg.accesses (p ++ q) = DistinctBilinProg.accesses p + DistinctBilinProg.accesses q := by
  induction p with
  | nil => simp [DistinctBilinProg.accesses]
  | cons i rest ih => cases i <;> simp [DistinctBilinProg.accesses, ih, Nat.add_assoc]

private theorem DistinctBilinProg.basicOps_append {n : Nat} (p q : List (DistinctBilinInstr n)) :
    DistinctBilinProg.basicOps (p ++ q) = DistinctBilinProg.basicOps p + DistinctBilinProg.basicOps q := by
  induction p with
  | nil => simp [DistinctBilinProg.basicOps]
  | cons i rest ih => cases i <;> simp [DistinctBilinProg.basicOps, ih, Nat.add_assoc]

private def liftFin {n : Nat} (i : Fin n) : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
private def swapReg (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

private theorem liftFin_inj {n : Nat} {a b : Fin n} (h : liftFin a = liftFin b) : a = b :=
  Fin.ext (congrArg (fun k : Fin (n + 1) => k.val) h)

private theorem liftFin_ne_swap {n : Nat} (a : Fin n) : liftFin a ≠ swapReg n := by
  intro h
  have hv : a.val = n := congrArg Fin.val h
  have hlt := a.isLt
  omega

private theorem swap_ne_liftFin {n : Nat} (a : Fin n) : swapReg n ≠ liftFin a :=
  (liftFin_ne_swap a).symm

private theorem swapReg_val_ne_zero {n : Nat} (a : Fin n) : (swapReg n).val ≠ 0 := by
  have hlt := a.isLt
  simp only [swapReg]
  omega

/-- Replace every `mulAdd dst a b` using an extra swap catalyst `swapReg n` when `a = b`. -/
public def translateBilinInstr {n : Nat} : BilinInstr n → List (DistinctBilinInstr (n + 1))
  | .addInput dst => [.addInput (liftFin dst)]
  | .mulAdd dst a b =>
    if a = b then
      [ .addReg (swapReg n) (liftFin a),
        .mulAdd (liftFin dst) (liftFin a) (swapReg n),
        .addReg (swapReg n) (liftFin a),
        .mulAdd (liftFin dst) (liftFin a) (swapReg n) ]
    else
      [.mulAdd (liftFin dst) (liftFin a) (liftFin b)]

/-- Translate a bilinear program to distinct operands using an auxiliary register. -/
public def translateBilinProg {n : Nat} : List (BilinInstr n) → List (DistinctBilinInstr (n + 1))
  | [] => []
  | i :: rest => translateBilinInstr i ++ translateBilinProg rest

/-- Strictly distinct-operand 2-access Frobenius program for `x^(2^k)` on `k + 2` registers. -/
public def frobDistinctProg (k : Nat) (hk : 1 ≤ k) : List (DistinctBilinInstr (k + 2)) :=
  translateBilinProg (frobBilinProg k hk)

private theorem translateBilinProg_accesses {n : Nat} (p : List (BilinInstr n)) :
    DistinctBilinProg.accesses (translateBilinProg p) = BilinProg.accesses p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | addInput dst =>
      simp [translateBilinProg, translateBilinInstr, DistinctBilinProg.accesses, BilinProg.accesses, ih]
    | mulAdd dst a b =>
      simp only [translateBilinProg, translateBilinInstr, DistinctBilinProg.accesses_append,
        BilinProg.accesses, ih]
      split <;> simp [DistinctBilinProg.accesses]

private theorem translateBilinProg_valid {n : Nat} (p : List (BilinInstr n))
    (hp : ∀ i ∈ p, i.isValidPassive) :
    ∀ j ∈ translateBilinProg p, j.isStrictValidPassive := by
  induction p with
  | nil => intro _ h; cases h
  | cons i rest ih =>
    intro j hj
    simp only [translateBilinProg, List.mem_append] at hj
    rcases hj with h1 | h2
    · have hi := hp i (List.mem_cons_self ..)
      cases i with
      | addInput dst =>
        simp only [translateBilinInstr, List.mem_singleton] at h1
        subst h1; trivial
      | mulAdd dst a b =>
        rcases hi with ⟨hda, hdb, ha0, hb0⟩
        simp only [translateBilinInstr] at h1
        split at h1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
          rcases h1 with rfl | rfl | rfl | rfl
          · exact ⟨swap_ne_liftFin a, ha0⟩
          · exact ⟨fun h => hda (liftFin_inj h), liftFin_ne_swap dst, liftFin_ne_swap a,
                   ha0, swapReg_val_ne_zero a⟩
          · exact ⟨swap_ne_liftFin a, ha0⟩
          · exact ⟨fun h => hda (liftFin_inj h), liftFin_ne_swap dst, liftFin_ne_swap a,
                   ha0, swapReg_val_ne_zero a⟩
        · rename_i hne
          simp only [List.mem_singleton] at h1
          subst h1
          exact ⟨fun h => hda (liftFin_inj h),
                 fun h => hdb (liftFin_inj h),
                 fun h => hne (liftFin_inj h),
                 ha0, hb0⟩
    · exact ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) j h2

private theorem translateBilinInstr_exec {n : Nat} {R : Type u} [Char2CRing R]
    (x : R) (instr : BilinInstr n) (hi : instr.isValidPassive) (st : Fin (n + 1) → R) :
    DistinctBilinProg.exec x (translateBilinInstr instr) st =
      fun i : Fin (n + 1) =>
        if h : i.val < n then
          instr.exec x (fun j : Fin n => st (liftFin j)) ⟨i.val, h⟩
        else
          st i := by
  cases instr with
  | addInput dst =>
    funext i
    simp only [translateBilinInstr, DistinctBilinProg.exec, DistinctBilinInstr.exec, BilinInstr.exec]
    by_cases hlt : i.val < n
    · simp only [hlt, ↓reduceDIte]
      by_cases hd : i = liftFin dst
      · subst hd
        simp [liftFin]
      · have hfin : (⟨i.val, hlt⟩ : Fin n) ≠ dst := fun h =>
          hd (Fin.ext (congrArg (fun k : Fin n => k.val) h))
        have hli : liftFin ⟨i.val, hlt⟩ = i := Fin.ext rfl
        simp [hd, hfin, hli]
    · have hne : i ≠ liftFin dst := fun h => hlt (by rw [h]; exact dst.isLt)
      simp [hlt, hne]
  | mulAdd dst a b =>
    rcases hi with ⟨hda, hdb, _, _⟩
    simp only [translateBilinInstr]
    split
    · rename_i hab; subst hab
      have ha_sw : liftFin a ≠ swapReg n := liftFin_ne_swap a
      have hsw_d : swapReg n ≠ liftFin dst := swap_ne_liftFin dst
      have hd_sw : liftFin dst ≠ swapReg n := liftFin_ne_swap dst
      have hd_a : liftFin dst ≠ liftFin a := fun h => hda (liftFin_inj h)
      have ha_d : liftFin a ≠ liftFin dst := hd_a.symm
      funext i
      simp only [DistinctBilinProg.exec, DistinctBilinInstr.exec, BilinInstr.exec]
      by_cases hsw : i = swapReg n
      · subst hsw
        have hnotlt : ¬ (swapReg n).val < n := by simp [swapReg]
        simp only [hnotlt, ↓reduceDIte, hsw_d, ha_sw, ha_d, ↓reduceIte]
        rw [CRing.add_assoc, Char2CRing.add_self, CRing.add_zero]
      · have hlt : i.val < n := by
          have hi_lt := i.isLt
          have hne : i.val ≠ n := fun h => hsw (Fin.ext h)
          omega
        simp only [hlt, ↓reduceDIte]
        by_cases hd : i = liftFin dst
        · subst hd
          have hd_fin : (⟨(liftFin dst).val, hlt⟩ : Fin n) = dst := Fin.ext rfl
          simp only [↓reduceIte, hsw_d, ha_sw, hd_sw, ha_d, hd_fin]
          have hrest : (st (swapReg n) + st (liftFin a)) + st (liftFin a) = st (swapReg n) := by
            rw [CRing.add_assoc, Char2CRing.add_self, CRing.add_zero]
          rw [hrest, CRing.left_distrib, CRing.add_assoc]
          congr 1
          calc
            (st (liftFin a) * st (swapReg n) + st (liftFin a) * st (liftFin a)) +
                st (liftFin a) * st (swapReg n)
                = (st (liftFin a) * st (swapReg n) + st (liftFin a) * st (swapReg n)) +
                    st (liftFin a) * st (liftFin a) := by
                  rw [CRing.add_assoc, CRing.add_comm (st (liftFin a) * st (liftFin a)), ← CRing.add_assoc]
            _ = 0 + st (liftFin a) * st (liftFin a) := by rw [Char2CRing.add_self]
            _ = st (liftFin a) * st (liftFin a) := CRing.zero_add _
        · have hd_fin : (⟨i.val, hlt⟩ : Fin n) ≠ dst := fun h =>
            hd (Fin.ext (congrArg (fun k : Fin n => k.val) h))
          have hli : liftFin ⟨i.val, hlt⟩ = i := Fin.ext rfl
          simp only [hd, hsw, hd_fin, hli, ↓reduceIte]
    · funext i
      simp only [DistinctBilinProg.exec, DistinctBilinInstr.exec, BilinInstr.exec]
      by_cases hlt : i.val < n
      · simp only [hlt, ↓reduceDIte]
        by_cases hd : i = liftFin dst
        · subst hd
          simp [liftFin]
        · have hfin : (⟨i.val, hlt⟩ : Fin n) ≠ dst := fun h =>
            hd (Fin.ext (congrArg (fun k : Fin n => k.val) h))
          have hli : liftFin ⟨i.val, hlt⟩ = i := Fin.ext rfl
          simp [hd, hfin, hli]
      · have hne : i ≠ liftFin dst := fun h => hlt (by rw [h]; exact dst.isLt)
        simp [hlt, hne]

private theorem translateBilinProg_exec {n : Nat} {R : Type u} [Char2CRing R]
    (x : R) (p : List (BilinInstr n)) (hp : ∀ i ∈ p, i.isValidPassive) (st : Fin (n + 1) → R) :
    DistinctBilinProg.exec x (translateBilinProg p) st =
      fun i : Fin (n + 1) =>
        if h : i.val < n then
          BilinProg.exec x p (fun j : Fin n => st (liftFin j)) ⟨i.val, h⟩
        else
          st i := by
  induction p generalizing st with
  | nil =>
    funext i
    simp only [translateBilinProg, DistinctBilinProg.exec, BilinProg.exec, liftFin]
    split <;> rfl
  | cons instr rest ih =>
    rw [translateBilinProg, DistinctBilinProg.exec_append,
        translateBilinInstr_exec x instr (hp instr (List.mem_cons_self ..)) st,
        ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]
    funext i
    simp only [BilinProg.exec]
    split
    · congr 1
      funext j
      simp [liftFin, j.isLt]
    · rfl

public theorem frobDistinctProg_accesses (k : Nat) (hk : 1 ≤ k) :
    DistinctBilinProg.accesses (frobDistinctProg k hk) = 2 := by
  rw [frobDistinctProg, translateBilinProg_accesses, frobBilinProg_accesses]

public theorem frobDistinctProg_valid (k : Nat) (hk : 1 ≤ k) :
    ∀ instr ∈ frobDistinctProg k hk, instr.isStrictValidPassive :=
  translateBilinProg_valid (frobBilinProg k hk) (frobBilinProg_valid k hk)

/-- **Theorem T2b (Strictly Distinct-Operand 2-Access Frobenius Collapse over Char 2):**
Adding one swap catalyst (`k + 2` registers total) eliminates all self-squares `R_a * R_a`
while keeping exact cleanliness and **EXACTLY 2 input accesses** for `x^(2^k)` over every `Char2CRing`. -/
public theorem frobDistinctProg_clean {R : Type u} [Char2CRing R] (k : Nat) (hk : 1 ≤ k)
    (x : R) (init : Fin (k + 2) → R) :
    let final := DistinctBilinProg.exec x (frobDistinctProg k hk) init
    final ⟨0, by omega⟩ = init ⟨0, by omega⟩ + CRing.pow x (2 ^ k) ∧
    ∀ i : Fin (k + 2), i.val ≠ 0 → final i = init i := by
  dsimp only
  rw [frobDistinctProg, translateBilinProg_exec x (frobBilinProg k hk) (frobBilinProg_valid k hk) init]
  have hclean := frobBilinProg_clean (R := R) k hk x (fun j : Fin (k + 1) => init (liftFin j))
  constructor
  · have hlt : (0 : Nat) < k + 1 := by omega
    simp only [hlt, ↓reduceDIte]
    exact hclean.1
  · intro i hi0
    by_cases hlt : i.val < k + 1
    · simp only [hlt, ↓reduceDIte]
      exact hclean.2 ⟨i.val, hlt⟩ hi0
    · simp only [hlt, ↓reduceDIte]

end Catalytic
