import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  `Chapter2.Nat`.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class `_root_.Nat`, or `ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the `*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's `Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's `Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's `Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's `Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  revert n; apply induction
  · rw [zero_mul]
  intro n ih; rw [succ_mul, ih, add_zero]

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's `Nat.mul_succ` -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  revert n; apply induction
  · rw [zero_mul, zero_mul, zero_add]
  intro n ih; rw [succ_mul, ih, succ_mul]
  rw [add_succ, add_succ]
  rw [add_assoc, add_assoc, add_comm n m]

/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's `Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  revert n; apply induction
  · rw [zero_mul, mul_zero]
  intro n ih; rw [succ_mul, mul_succ, ih]

/-- Compare with Mathlib's `Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's `Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  apply uniq_succ_eq at h₁; apply uniq_succ_eq at h₂
  obtain ⟨a, rfl, h2⟩ := h₁
  obtain ⟨b, rfl, h4⟩ := h₂
  rw [succ_mul, add_succ]
  apply succ_ne

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's `Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor <;> intro h
  · contrapose! h; apply pos_mul_pos; apply h.1; apply h.2
  rcases h with (rfl | rfl); rw [zero_mul]; rw [mul_zero]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's `Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's `Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's `Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert c; apply induction
  · repeat rw [mul_zero]
  intro c ih
  rw [mul_succ, mul_succ, mul_add, ih]

/-- (Not from textbook)  Nat is a commutative semiring.
    This allows tactics such as `ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the `ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's `Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  rw [lt_iff_add_pos] at *
  obtain ⟨d, hd, rfl⟩ := h
  refine ⟨d * c, pos_mul_pos hd hc, by ring⟩

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's `Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's `Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  rcases trichotomous a b with hlt | rfl | hgt
  · replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  · rfl
  · replace hgt := mul_gt_mul_of_pos_right hgt hc
    apply ne_of_gt at hgt
    contradiction

/-
∀ (a b c : Nat), a ≤ b → 0 ≤ c → c * a ≤ c * b
-/
lemma Nat.mul_le_mul_of_nonneg_left' (a b c : Nat) (hab : a ≤ b) (_ : 0 ≤ c) : c * a ≤ c * b := by
  obtain ⟨d, rfl⟩ := hab; exact ⟨c*d, by ring⟩
/-- (Not from textbook) Nat is an ordered semiring.
This allows tactics such as `gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := ⟨1, by ring⟩
  mul_le_mul_of_nonneg_left := mul_le_mul_of_nonneg_left'
  mul_le_mul_of_nonneg_right := by
    intros; rw [mul_comm]; nth_rw 2 [mul_comm]
    apply mul_le_mul_of_nonneg_left'; repeat assumption

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr <;> apply Nat.zero_le


lemma Nat.isPos_iff_gt_zero {n: Nat} : n.IsPos ↔ n > 0 := by
  rw [gt_iff, isPos_iff]; simp

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's `Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  revert n; apply induction
  · refine ⟨0,0, by simp; apply isPos_iff_gt_zero.mp hq⟩
  intro n ih
  obtain ⟨m, r, hr, hrq, hih⟩ := ih
  by_cases hrpq : r++ ≠ q <;> subst hih
  · refine ⟨m, r++, zero_le _, ?_, by rw [add_succ]⟩
    rw [Nat.lt_iff_succ_le] at hrq; order
  · refine ⟨m++, 0, zero_le _, isPos_iff_gt_zero.mp hq, ?_, ⟩
    push_neg at hrpq; subst hrpq
    rw [← add_succ, ← succ_mul, add_zero]

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's `Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's `Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's `Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

theorem Nat.pow_two (m: Nat) : m ^ (2:Nat) = m * m := by
  rw [←one_succ, pow_succ, pow_one]

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  rw [pow_two]; ring; rfl

end Chapter2
