/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.CommRing

/-!
# Theorem T4: Balanced Zero-Workspace Bilinear Multilinear Product

Over any commutative ring `R`, for every `k ≥ 1` and `d = 2^k`, we construct an explicit
zero-workspace bilinear catalytic register program computing the `d`-fold multilinear
product `x_0 * x_1 * ... * x_{d-1}` using:
  * **Zero clean workspace** (all registers start at arbitrary catalytic values),
  * Only `k + 2 = log_2(d) + 2` total registers (1 target + `k + 1` catalysts),
  * Strictly distinct operand indices (`dst ≠ a`, `dst ≠ b`, `a ≠ b`),
  * Exact primitive instruction count `ops(k)` satisfying `3 * ops(k) + 4 = 7 * (2^k)^2`,
    i.e. `ops(k) = (7 * d^2 - 4) / 3 = O(d^2)` (exponentially improving over the linear
    chain `3 * 4^(d-1) - 2` in both op count and register count `d` vs `log_2(d) + 2`).
-/

namespace Catalytic

universe u

/-- Primitive bilinear / signed-input catalytic instruction on arbitrary natural-indexed registers. -/
public inductive CatOp where
  /-- `R_dst ← R_dst + sign * x_{varIdx}` (`sign ∈ {1, -1}`). -/
  | addInput (dst : Nat) (sign : Int) (varIdx : Nat) : CatOp
  /-- `R_dst ← R_dst + sign * R_a * R_b` (`sign ∈ {1, -1}`). -/
  | addProd (dst a b : Nat) (sign : Int) : CatOp
  deriving DecidableEq, Repr

/-- Strictly valid distinct-index instruction check (`sign ∈ {1, -1}` and `dst, a, b` pairwise distinct). -/
public def CatOp.isStrictValid : CatOp → Prop
  | .addInput _ s _ => s = 1 ∨ s = -1
  | .addProd dst a b s => (s = 1 ∨ s = -1) ∧ dst ≠ a ∧ dst ≠ b ∧ a ≠ b

/-- Every register read or written by `op` lies inside the designated register list `regs`. -/
public def CatOp.usesOnly (regs : List Nat) : CatOp → Prop
  | .addInput dst _ _ => dst ∈ regs
  | .addProd dst a b _ => dst ∈ regs ∧ a ∈ regs ∧ b ∈ regs

/-- Execute one `CatOp` over any commutative ring `R`. -/
public def CatOp.exec {R : Type u} [CRing R] (xs : Nat → R) (st : Nat → R) : CatOp → (Nat → R)
  | .addInput dst s v =>
    fun r => if r = dst then st dst + CRing.intCast s * xs v else st r
  | .addProd dst a b s =>
    fun r => if r = dst then st dst + CRing.intCast s * (st a * st b) else st r

/-- Execute a list of `CatOp` instructions left-to-right. -/
public def CatProg.exec {R : Type u} [CRing R] (xs : Nat → R) : List CatOp → (Nat → R) → (Nat → R)
  | [], st => st
  | op :: rest, st => CatProg.exec xs rest (op.exec xs st)

theorem CatProg.exec_append {R : Type u} [CRing R]
    (xs : Nat → R) (p q : List CatOp) (st : Nat → R) :
    CatProg.exec xs (p ++ q) st = CatProg.exec xs q (CatProg.exec xs p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons op rest ih => exact ih (op.exec xs st)

/-- Product of `n` consecutive inputs starting at `offset`: `∏_{i < n} xs (offset + i)`. -/
public def rangeProd {R : Type u} [CRing R] (xs : Nat → R) (offset : Nat) : Nat → R
  | 0 => 1
  | n + 1 => rangeProd xs offset n * xs (offset + n)

theorem rangeProd_add {R : Type u} [CRing R] (xs : Nat → R) (offset a b : Nat) :
    rangeProd xs offset (a + b) = rangeProd xs offset a * rangeProd xs (offset + a) b := by
  induction b with
  | zero => simp [rangeProd]
  | succ m ih =>
    have h1 : a + (m + 1) = (a + m) + 1 := by omega
    rw [h1, rangeProd, ih, rangeProd, CRing.mul_assoc]
    have h2 : offset + (a + m) = offset + a + m := by omega
    rw [h2]

/--
Balanced recursive zero-workspace catalytic product program for `2^k` inputs.
Requires `pool.length ≥ k + 1` (for `k ≥ 1`; for `k = 0`, `pool` can be empty).
-/
public def balancedProdProg : (k : Nat) → (target : Nat) → (sign : Int) →
    (pool : List Nat) → (offset : Nat) → List CatOp
  | 0, target, sign, _, offset =>
    [.addInput target sign offset]
  | k + 1, target, sign, ra :: rb :: rest, offset =>
    let half := 2 ^ k
    [.addProd target ra rb sign] ++
    balancedProdProg k ra 1 (rb :: rest) offset ++
    [.addProd target ra rb (-sign)] ++
    balancedProdProg k rb 1 (ra :: rest) (offset + half) ++
    [.addProd target ra rb sign] ++
    balancedProdProg k ra (-1) (rb :: rest) offset ++
    [.addProd target ra rb (-sign)] ++
    balancedProdProg k rb (-1) (ra :: rest) (offset + half)
  | _ + 1, _, _, _, _ => []

/-- Exact instruction count of `balancedProdProg`: satisfies `T(0) = 1`, `T(k+1) = 4 * T(k) + 4`. -/
public def balancedOpCount : Nat → Nat
  | 0 => 1
  | k + 1 => 4 * balancedOpCount k + 4

/-- Closed-form quadratic identity: `3 * balancedOpCount k + 4 = 7 * (2^k)^2`. -/
public theorem balancedOpCount_formula (k : Nat) :
    3 * balancedOpCount k + 4 = 7 * (2 ^ k) ^ 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [balancedOpCount]
    have hpow : (2 ^ (k + 1)) ^ 2 = 4 * (2 ^ k) ^ 2 := by
      have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by omega
      rw [h1, Nat.pow_two, Nat.pow_two]
      have hmul : (2 * 2 ^ k) * (2 * 2 ^ k) = 4 * (2 ^ k * 2 ^ k) := by
        calc
          (2 * 2 ^ k) * (2 * 2 ^ k)
              = 2 * (2 ^ k * (2 * 2 ^ k)) := Nat.mul_assoc _ _ _
          _   = 2 * ((2 * 2 ^ k) * 2 ^ k) := by rw [Nat.mul_comm (2 ^ k) (2 * 2 ^ k)]
          _   = 2 * (2 * (2 ^ k * 2 ^ k)) := by rw [Nat.mul_assoc 2 (2 ^ k) (2 ^ k)]
          _   = (2 * 2) * (2 ^ k * 2 ^ k) := (Nat.mul_assoc _ _ _).symm
          _   = 4 * (2 ^ k * 2 ^ k) := rfl
      exact hmul
    rw [hpow]
    omega

/-- Exact length equality: `(balancedProdProg k target sign pool offset).length = balancedOpCount k`. -/
public theorem balancedProdProg_length (k target : Nat) (sign : Int)
    (pool : List Nat) (offset : Nat) (hpool : k = 0 ∨ k + 1 ≤ pool.length) :
    (balancedProdProg k target sign pool offset).length = balancedOpCount k := by
  induction k generalizing target sign pool offset with
  | zero => rfl
  | succ k ih =>
    have hlen : k + 2 ≤ pool.length := by
      rcases hpool with h0 | h1
      · omega
      · exact h1
    match pool with
    | [] => simp at hlen
    | [_] => simp at hlen
    | ra :: rb :: rest =>
      simp only [balancedProdProg, balancedOpCount, List.length_append, List.length_singleton]
      have hsub : k = 0 ∨ k + 1 ≤ (rb :: rest).length := by
        right; simp at hlen ⊢; omega
      have hsub2 : k = 0 ∨ k + 1 ≤ (ra :: rest).length := by
        right; simp at hlen ⊢; omega
      rw [ih ra 1 (rb :: rest) offset hsub,
          ih rb 1 (ra :: rest) (offset + 2 ^ k) hsub2,
          ih ra (-1) (rb :: rest) offset hsub,
          ih rb (-1) (ra :: rest) (offset + 2 ^ k) hsub2]
      omega

/-- Every instruction emitted by `balancedProdProg` has strictly valid signs and pairwise distinct registers. -/
public theorem balancedProdProg_strictValid (k target : Nat) (sign : Int)
    (pool : List Nat) (offset : Nat)
    (hsign : sign = 1 ∨ sign = -1)
    (hpool : k = 0 ∨ k + 1 ≤ pool.length)
    (hnd : (target :: pool).Nodup) :
    ∀ op ∈ balancedProdProg k target sign pool offset, op.isStrictValid := by
  induction k generalizing target sign pool offset with
  | zero =>
    intro op hop
    simp only [balancedProdProg, List.mem_singleton] at hop
    subst hop
    exact hsign
  | succ k ih =>
    have hlen : k + 2 ≤ pool.length := by
      rcases hpool with h0 | h1
      · omega
      · exact h1
    match pool with
    | [] => simp at hlen
    | [_] => simp at hlen
    | ra :: rb :: rest =>
      have hneg : -sign = 1 ∨ -sign = -1 := by rcases hsign with rfl | rfl <;> omega
      rw [List.nodup_cons] at hnd
      obtain ⟨ht_not_in, hnd_pool⟩ := hnd
      rw [List.nodup_cons] at hnd_pool
      obtain ⟨hra_not_in, hnd_rb_rest⟩ := hnd_pool
      have hta : target ≠ ra := fun h => ht_not_in (by simp [h])
      have htb : target ≠ rb := fun h => ht_not_in (by simp [h])
      have hab : ra ≠ rb := fun h => hra_not_in (by simp [h])
      have hnd_a : (ra :: rb :: rest).Nodup := List.nodup_cons.mpr ⟨hra_not_in, hnd_rb_rest⟩
      have hnd_b : (rb :: ra :: rest).Nodup := by
        rw [List.nodup_cons] at hnd_rb_rest ⊢
        obtain ⟨hrb_not_rest, hnd_rest⟩ := hnd_rb_rest
        refine ⟨?_, List.nodup_cons.mpr ⟨fun h => hra_not_in (List.mem_cons_of_mem rb h), hnd_rest⟩⟩
        simp only [List.mem_cons, not_or]
        exact ⟨hab.symm, hrb_not_rest⟩
      have hsub1 : k = 0 ∨ k + 1 ≤ (rb :: rest).length := by right; simp at hlen ⊢; omega
      have hsub2 : k = 0 ∨ k + 1 ≤ (ra :: rest).length := by right; simp at hlen ⊢; omega
      intro op hop
      simp only [balancedProdProg, List.mem_append, List.mem_singleton] at hop
      rcases hop with (((((((rfl | h) | rfl) | h) | rfl) | h) | rfl) | h)
      · exact ⟨hsign, hta, htb, hab⟩
      · exact ih ra 1 (rb :: rest) offset (Or.inl rfl) hsub1 hnd_a op h
      · exact ⟨hneg, hta, htb, hab⟩
      · exact ih rb 1 (ra :: rest) (offset + 2 ^ k) (Or.inl rfl) hsub2 hnd_b op h
      · exact ⟨hsign, hta, htb, hab⟩
      · exact ih ra (-1) (rb :: rest) offset (Or.inr rfl) hsub1 hnd_a op h
      · exact ⟨hneg, hta, htb, hab⟩
      · exact ih rb (-1) (ra :: rest) (offset + 2 ^ k) (Or.inr rfl) hsub2 hnd_b op h

private theorem CatOp.usesOnly_mono {r1 r2 : List Nat} (hsub : ∀ x ∈ r1, x ∈ r2) :
    ∀ op : CatOp, op.usesOnly r1 → op.usesOnly r2
  | .addInput _ _ _, h => hsub _ h
  | .addProd _ _ _ _, ⟨h1, h2, h3⟩ => ⟨hsub _ h1, hsub _ h2, hsub _ h3⟩

/-- The designated register list for level `k` has at most `k + 2` registers (`1` for `k = 0`). -/
public theorem designatedRegs_length_le (k target : Nat) (pool : List Nat) :
    (if k = 0 then [target] else target :: pool.take (k + 1)).length ≤ k + 2 := by
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk, List.length_take]; omega

/-- Every instruction emitted by `balancedProdProg` reads and writes ONLY registers inside
the designated `≤ k + 2` register set `if k = 0 then [target] else target :: pool.take (k + 1)`. -/
public theorem balancedProdProg_usesOnly (k target : Nat) (sign : Int)
    (pool : List Nat) (offset : Nat) :
    ∀ op ∈ balancedProdProg k target sign pool offset,
      op.usesOnly (if k = 0 then [target] else target :: pool.take (k + 1)) := by
  induction k generalizing target sign pool offset with
  | zero =>
    intro op hop
    simp only [balancedProdProg, List.mem_singleton] at hop
    subst hop
    simp [CatOp.usesOnly]
  | succ k ih =>
    match pool with
    | [] => intro op hop; simp [balancedProdProg] at hop
    | [_] => intro op hop; simp [balancedProdProg] at hop
    | ra :: rb :: rest =>
      have hsubA : ∀ x ∈ (if k = 0 then [ra] else ra :: (rb :: rest).take (k + 1)),
          x ∈ target :: (ra :: rb :: rest).take (k + 2) := by
        intro x hx
        by_cases hk : k = 0
        · simp [hk] at hx; subst hx; simp [List.take]
        · simp [hk, List.take] at hx ⊢
          rcases hx with rfl | rfl | hrest
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr hrest))
      have hsubB : ∀ x ∈ (if k = 0 then [rb] else rb :: (ra :: rest).take (k + 1)),
          x ∈ target :: (ra :: rb :: rest).take (k + 2) := by
        intro x hx
        by_cases hk : k = 0
        · simp [hk] at hx; subst hx; simp [List.take]
        · simp [hk, List.take] at hx ⊢
          rcases hx with rfl | rfl | hrest
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr hrest))
      have htop : ∀ s : Int,
          (CatOp.addProd target ra rb s).usesOnly (target :: (ra :: rb :: rest).take (k + 2)) := by
        intro s
        simp [CatOp.usesOnly, List.take]
      intro op hop
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      simp only [balancedProdProg, List.mem_append, List.mem_singleton] at hop
      rcases hop with (((((((rfl | h) | rfl) | h) | rfl) | h) | rfl) | h)
      · exact htop sign
      · exact CatOp.usesOnly_mono hsubA op (ih ra 1 (rb :: rest) offset op h)
      · exact htop (-sign)
      · exact CatOp.usesOnly_mono hsubB op (ih rb 1 (ra :: rest) (offset + 2 ^ k) op h)
      · exact htop sign
      · exact CatOp.usesOnly_mono hsubA op (ih ra (-1) (rb :: rest) offset op h)
      · exact htop (-sign)
      · exact CatOp.usesOnly_mono hsubB op (ih rb (-1) (ra :: rest) (offset + 2 ^ k) op h)

/-- Core 8-step commutator algebraic cancellation identity over ANY commutative ring `R`. -/
private theorem commutator_algebra {R : Type u} [CRing R]
    (o a b A B s : R) :
    ((((o + s * (a * b)) + (-s) * ((a + A) * b)) + s * ((a + A) * (b + B))) +
      (-s) * (a * (b + B))) = o + s * (A * B) := by
  have h1 : (a + A) * b = a * b + A * b := CRing.right_distrib a A b
  have h2 : (a + A) * (b + B) = (a * b + a * B) + (A * b + A * B) := by
    rw [CRing.right_distrib, CRing.left_distrib, CRing.left_distrib]
  have h3 : a * (b + B) = a * b + a * B := CRing.left_distrib a b B
  rw [h1, h2, h3]
  -- Distribute s and -s and cancel pairwise using CRing laws
  have hsneg : ∀ z : R, (-s) * z = -(s * z) := fun z => CRing.neg_mul s z
  simp only [CRing.left_distrib, hsneg, CRing.neg_add_rev]
  -- Collect the 4 pairs of opposite terms cleanly!
  let t1 := s * (a * b)
  let t2 := s * (A * b)
  let t3 := s * (a * B)
  let t4 := s * (A * B)
  change (((o + t1) + (-t1 + -t2)) + ((t1 + t3) + (t2 + t4))) + (-t1 + -t3) = o + t4
  have hc1 : (o + t1) + (-t1 + -t2) = o + -t2 := by
    rw [CRing.add_assoc, ← CRing.add_assoc t1 (-t1), CRing.add_neg, CRing.zero_add]
  rw [hc1]
  have hc2 : (o + -t2) + ((t1 + t3) + (t2 + t4)) = ((o + t1) + t3) + t4 := by
    calc
      (o + -t2) + ((t1 + t3) + (t2 + t4))
          = o + (-t2 + ((t1 + t3) + (t2 + t4))) := CRing.add_assoc _ _ _
      _   = o + (((t1 + t3) + (-t2 + t2)) + t4) := by
            congr 1
            calc
              -t2 + ((t1 + t3) + (t2 + t4))
                  = (-t2 + (t1 + t3)) + (t2 + t4) := (CRing.add_assoc _ _ _).symm
              _   = ((t1 + t3) + -t2) + (t2 + t4) := by rw [CRing.add_comm (-t2) (t1 + t3)]
              _   = ((t1 + t3) + (-t2 + t2)) + t4 := by
                    rw [CRing.add_assoc (t1 + t3) (-t2) (t2 + t4),
                        ← CRing.add_assoc (-t2) t2 t4,
                        ← CRing.add_assoc (t1 + t3)]
      _   = o + ((t1 + t3) + t4) := by rw [CRing.neg_add, CRing.add_zero]
      _   = ((o + t1) + t3) + t4 := by rw [← CRing.add_assoc, ← CRing.add_assoc]
  rw [hc2]
  calc
    (((o + t1) + t3) + t4) + (-t1 + -t3)
        = ((((o + t1) + t3) + -t3) + -t1) + t4 := by
          calc
            (((o + t1) + t3) + t4) + (-t1 + -t3)
                = (((o + t1) + t3) + (-t1 + -t3)) + t4 := by
                  rw [CRing.add_assoc ((o + t1) + t3) t4 (-t1 + -t3),
                      CRing.add_comm t4 (-t1 + -t3),
                      ← CRing.add_assoc]
            _   = ((((o + t1) + t3) + -t3) + -t1) + t4 := by
                  rw [CRing.add_comm (-t1) (-t3), ← CRing.add_assoc ((o + t1) + t3)]
    _   = ((o + t1) + -t1) + t4 := by
          rw [CRing.add_assoc (o + t1) t3 (-t3), CRing.add_neg, CRing.add_zero]
    _   = o + t4 := by
          rw [CRing.add_assoc o t1 (-t1), CRing.add_neg, CRing.add_zero]

/--
**Theorem T4 (Clean Execution of Balanced Zero-Workspace Multilinear Catalytic Product).**
For every `k : Nat`, every commutative ring `R`, arbitrary inputs `xs : Nat → R`,
arbitrary initial catalytic register state `st : Nat → R`, and any distinct register
list `target :: pool` with `pool.length ≥ k + 1` (for `k ≥ 1`), executing
`balancedProdProg k target sign pool offset` adds `sign * ∏_{i < 2^k} xs (offset + i)`
to register `target` and restores EVERY other register `r ≠ target` bit-for-bit!
-/
public theorem balancedProdProg_clean {R : Type u} [CRing R]
    (k target : Nat) (sign : Int) (pool : List Nat) (offset : Nat)
    (hpool : k = 0 ∨ k + 1 ≤ pool.length)
    (hnd : (target :: pool).Nodup)
    (xs : Nat → R) (st : Nat → R) :
    CatProg.exec xs (balancedProdProg k target sign pool offset) st =
      (fun r => if r = target then st target + CRing.intCast sign * rangeProd xs offset (2 ^ k)
                else st r) := by
  induction k generalizing target sign pool offset st with
  | zero =>
    funext r
    simp [balancedProdProg, CatProg.exec, CatOp.exec, rangeProd, CRing.one_mul]
  | succ k ih =>
    have hlen : k + 2 ≤ pool.length := by
      rcases hpool with h0 | h1
      · omega
      · exact h1
    match pool with
    | [] => simp at hlen
    | [_] => simp at hlen
    | ra :: rb :: rest =>
      rw [List.nodup_cons] at hnd
      obtain ⟨ht_not_in, hnd_pool⟩ := hnd
      rw [List.nodup_cons] at hnd_pool
      obtain ⟨hra_not_in, hnd_rb_rest⟩ := hnd_pool
      have hta : target ≠ ra := fun h => ht_not_in (by simp [h])
      have htb : target ≠ rb := fun h => ht_not_in (by simp [h])
      have hab : ra ≠ rb := fun h => hra_not_in (by simp [h])
      have hnd_a : (ra :: rb :: rest).Nodup := List.nodup_cons.mpr ⟨hra_not_in, hnd_rb_rest⟩
      have hnd_b : (rb :: ra :: rest).Nodup := by
        rw [List.nodup_cons] at hnd_rb_rest ⊢
        obtain ⟨hrb_not_rest, hnd_rest⟩ := hnd_rb_rest
        refine ⟨?_, List.nodup_cons.mpr ⟨fun h => hra_not_in (List.mem_cons_of_mem rb h), hnd_rest⟩⟩
        simp only [List.mem_cons, not_or]
        exact ⟨hab.symm, hrb_not_rest⟩
      have hsub1 : k = 0 ∨ k + 1 ≤ (rb :: rest).length := by right; simp at hlen ⊢; omega
      have hsub2 : k = 0 ∨ k + 1 ≤ (ra :: rest).length := by right; simp at hlen ⊢; omega
      let A := rangeProd xs offset (2 ^ k)
      let B := rangeProd xs (offset + 2 ^ k) (2 ^ k)
      let s := (CRing.intCast sign : R)
      have hneg_s : (CRing.intCast (-sign) : R) = -s := CRing.intCast_neg sign
      simp only [balancedProdProg, CatProg.exec_append]
      -- Step through all 8 stages explicitly!
      rw [ih ra 1 (rb :: rest) offset hsub1 hnd_a]
      rw [ih rb 1 (ra :: rest) (offset + 2 ^ k) hsub2 hnd_b]
      rw [ih ra (-1) (rb :: rest) offset hsub1 hnd_a]
      rw [ih rb (-1) (ra :: rest) (offset + 2 ^ k) hsub2 hnd_b]
      funext r
      simp only [CatProg.exec, CatOp.exec, CRing.intCast_one, CRing.one_mul,
        CRing.intCast_neg_one, CRing.neg_mul, hneg_s]
      by_cases hrt : r = target
      · rw [hrt]
        simp only [hta.symm, htb.symm, hta, htb, hab, hab.symm, ↓reduceIte]
        have h1 : st ra + A + -A = st ra := by
          rw [CRing.add_assoc, CRing.add_neg, CRing.add_zero]
        have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
        rw [hpow2, rangeProd_add]
        have hcomm := commutator_algebra (st target) (st ra) (st rb) A B s
        simp only [CRing.neg_mul] at hcomm
        change ((((st target + s * (st ra * st rb)) + -(s * ((st ra + A) * st rb))) +
            s * ((st ra + A) * (st rb + B))) +
            -(s * ((st ra + A + -A) * (st rb + B)))) = st target + s * (A * B)
        rw [h1]
        exact hcomm
      · by_cases hra : r = ra
        · subst hra
          simp only [hrt, hab, ↓reduceIte]
          rw [CRing.add_assoc, CRing.add_neg, CRing.add_zero]
        · by_cases hrb : r = rb
          · subst hrb
            simp only [hrt, hab.symm, ↓reduceIte]
            rw [CRing.add_assoc, CRing.add_neg, CRing.add_zero]
          · simp [hrt, hra, hrb]

end Catalytic
