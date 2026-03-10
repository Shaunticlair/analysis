import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro x; rfl
    symm := by intro a b h; symm; exact h
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor <;> intro h
  · rw [← Int.natCast_inj, h]; rfl
  · rw [h]; rfl

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
  intro ⟨a1, a2⟩ ⟨b1,b2⟩ h1; simp at h1
  simp [Setoid.r] at * -- Simplify the equivalence relation
  symm; nth_rw 1 [add_comm]; nth_rw 2 [add_comm]
  exact h1)

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

lemma Int.n_n_eq_zero (n:ℕ) : (n —— n) = 0 := by
  rw [ofNat_eq, eq]; abel

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms
  (by intro a b c;
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
      obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
      obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
      repeat rw [add_eq]
      rw [Int.eq]; abel)
  (by intro a; -- zero_add
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
      rw [ofNat_eq, add_eq]; simp)
  (by intro a; -- add_left_neg
      obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
      rw [neg_eq, add_eq]; abel_nf;
      apply Int.n_n_eq_zero _)

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro a b;
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    repeat rw [add_eq]
    abel_nf

lemma Int.mul_comm' (a b:Int) : a * b = b * a := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  repeat rw [mul_eq]
  rw [eq]; ring

lemma Int.one_mul' (a:Int) : 1 * a = a := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [ofNat_eq, mul_eq]; simp

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := mul_comm'

  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := one_mul'
  mul_one := by intro a; rw [mul_comm', one_mul']

lemma Int.left_distrib' (a b c:Int) : a * (b + c) = a * b + a * c := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
  rw [add_eq]; repeat rw [mul_eq];
  rw [add_eq]; congr 1 <;> ring

lemma Int.zero_mul' (a:Int) : 0 * a = 0 := by
  obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
  rw [ofNat_eq, mul_eq]; simp
/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := Int.left_distrib'
  right_distrib := by
    intro a b c
    rw [mul_comm]
    rw [Int.left_distrib']
    rw [mul_comm a c, mul_comm b c]
  zero_mul := zero_mul'
  mul_zero := by
    intro a; rw [mul_comm, zero_mul']

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  rw [Int.sub_eq]; repeat rw [natCast_eq]
  rw [neg_eq, add_eq]; simp

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
lemma Int.nonzero_imp_pos_or_neg (a : Int) (h : a ≠ 0) : a.IsPos ∨ a.IsNeg := by
  rcases a.trichotomous with h | h | h
  · contradiction
  · left; exact h
  · right; exact h

lemma Int.pos_mul_pos_eq_pos (a b : Int) (ha : a.IsPos) (hb : b.IsPos) : (a * b).IsPos := by
  obtain ⟨ a, ha, rfl ⟩ := ha
  obtain ⟨ b, hb, rfl ⟩ := hb
  use a * b; simp_all

lemma Int.pos_mul_neg_eq_neg (a b : Int) (ha : a.IsPos) (hb : b.IsNeg) : (a * b).IsNeg := by
  obtain ⟨ a, ha, rfl ⟩ := ha
  obtain ⟨ b, hb, rfl ⟩ := hb
  use a * b; simp_all

lemma Int.neg_mul_neg_eq_pos (a b : Int) (ha : a.IsNeg) (hb : b.IsNeg) : (a * b).IsPos := by
  obtain ⟨ a, ha, rfl ⟩ := ha
  obtain ⟨ b, hb, rfl ⟩ := hb
  use a * b; simp_all

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  contrapose! h
  have ha := Int.nonzero_imp_pos_or_neg a h.1
  have hb := Int.nonzero_imp_pos_or_neg b h.2
  simp;
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> by_contra heq
  · have := Int.pos_mul_pos_eq_pos a b ha hb
    apply not_pos_zero _ ⟨heq, this⟩
  · have := Int.pos_mul_neg_eq_neg a b ha hb
    apply not_neg_zero _ ⟨heq, this⟩
  · have := Int.pos_mul_neg_eq_neg b a hb ha
    rw [mul_comm] at heq
    apply not_neg_zero _ ⟨heq, this⟩
  · have := Int.neg_mul_neg_eq_pos a b ha hb
    apply not_pos_zero _ ⟨heq, this⟩


lemma Int.neg_eq_mul_neg_one : ∀ a : Int, -a = -1 * a := by
  intro a
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  rw [ofNat_eq, neg_eq, neg_eq, mul_eq]
  simp


-- This has a built-in version from our above proven infrastructure,
-- But I figured it was more in the spirit to do it manually
lemma Int.sub_eq_zero' (a b : Int) : a - b = 0 ↔ a = b := by
  constructor <;> intro h
  · have : a - b + b = b := by rw [h, zero_add]
    simp at this; exact this
  · simp [h]

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have : a * c - b * c = 0 := by simp [h]
  rw [sub_eq, neg_eq_mul_neg_one, ← mul_assoc] at this
  rw [← right_distrib] at this
  apply mul_eq_zero at this
  simp [hc] at this
  rw [← sub_eq] at this
  rw [sub_eq_zero] at this; exact this

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) :
a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor <;> intro h
  · rw [lt_iff] at h;
    obtain ⟨ ⟨t, ht⟩, hab ⟩ := h
    use t
    rw [ht]; simp
    by_contra h0; rw [h0] at ht; simp at ht;
    symm at ht; contradiction
  · choose n hn using h
    rw [lt_iff]
    simp [hn,cast_eq_0_iff_eq_0]

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := h
  use n; simp [h1, h2]; abel

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := hab
  obtain ⟨m, ⟨h3,h4⟩ ⟩ := hc
  simp at h4
  use n*m
  simp_all
  rw [right_distrib]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := h
  use n; simp [h1, h2]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  obtain ⟨n, hn⟩ := h
  use n; simp [hn]

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference] at *
  obtain ⟨n, ⟨h1,h2⟩ ⟩ := hab
  obtain ⟨m, ⟨h3,h4⟩ ⟩ := hbc
  use n + m;
  constructor
  · simp; tauto
  · rw [h2] at h4; rw [h4];
    simp; rw [add_assoc]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  have := trichotomous ( a - b )
  rcases this with (h | h | h)
  · right; right; rw [sub_eq_zero'] at h; exact h
  · left; obtain ⟨n, ⟨h1,h2⟩⟩ := h
    -- Flip a > b to b < a
    change b < a
    rw [lt_iff_exists_positive_difference]
    use n
    constructor
    · by_contra h; rw [h] at h1;
      simp_all -- Overdoing it the first time
    · simp [← h2]

  · right; left
    obtain ⟨n, ⟨h1,h2⟩⟩ := h
    rw [lt_iff_exists_positive_difference]
    use n
    constructor
    · exact ne_of_gt h1 -- Not overdoing it this time
    · have : a - b + b = -n + b := by rw [h2]
      simp at this; simp [this]

lemma Int.a_lt_b_imp_pos_diff {a b : Int} (h : a < b) :
IsPos (b - a) := by
  rw [lt_iff_exists_positive_difference] at h
  obtain ⟨n, ⟨hn1, hn2⟩⟩ := h
  unfold IsPos; use n
  constructor
  · apply Nat.pos_of_ne_zero hn1
  · rw [hn2]; simp

lemma Int.neg_pos_is_neg {a : Int} (h : IsPos a) : IsNeg (-a) := by
  obtain ⟨n, ⟨hn1, hn2⟩⟩ := h
  unfold IsNeg; use n
  constructor
  · use hn1
  · rw [hn2]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  change ¬ (b < a ∧ a < b)
  intro ⟨h1,h2⟩
  apply a_lt_b_imp_pos_diff at h1
  apply a_lt_b_imp_pos_diff at h2
  apply neg_pos_is_neg at h2
  simp at h2
  apply not_pos_neg (a-b); exact And.intro h1 h2

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  change ¬ (b < a ∧ a = b)
  intro ⟨h1,h2⟩
  apply a_lt_b_imp_pos_diff at h1
  rw [← sub_eq_zero'] at h2
  apply not_pos_zero (a-b); exact And.intro h2 h1

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  intro ⟨h1,h2⟩
  apply a_lt_b_imp_pos_diff at h1
  rw [← sub_eq_zero'] at h2
  apply neg_pos_is_neg at h1; simp at h1
  apply not_neg_zero (a-b); exact And.intro h2 h1

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        rw [le_iff]
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
        use t
        rw [natCast_eq, add_eq, eq]
        simp; rw [add_comm]; rw [ht]; abel
      | isFalse h =>
        apply isFalse
        contrapose! h
        rw [le_iff] at h
        choose t ht using h
        rw [natCast_eq, add_eq, eq] at ht
        simp at ht;
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor <;> intro h
  · specialize h 0; rw [h]; simp
  · rw [h]; simp

lemma Int.le_antisymm' (a b : Int) : (a ≤ b) → (b ≤ a) →  a = b := by
  intro h1 h2
  obtain ⟨ t, ht ⟩ := h1
  obtain ⟨ s, hs ⟩ := h2
  rw [ht] at hs; symm at hs
  rw [add_assoc,add_eq_left] at hs
  rw [natCast_eq, natCast_eq, ofNat_eq] at hs
  rw [add_eq, eq] at hs; simp at hs
  have : t = 0 := by omega
  simp [this] at ht; exact ht.symm


/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by intro a; use 0; simp
  le_trans := by
    intro a b c hab hbc;
    obtain ⟨ t1, ht1 ⟩ := hab
    obtain ⟨ t2, ht2 ⟩ := hbc
    use t1 + t2; simp [ht1, ht2]; abel
  lt_iff_le_not_ge := by
    intro a b; constructor <;> intro h
    · constructor
      · rw [lt_iff] at h; exact h.1
      · rw [lt_iff] at h; obtain ⟨h1,hba⟩ := h
        contrapose! hba
        have hab: a ≤ b := by choose t _ using h1; use t
        apply le_antisymm' _ _ hab hba

    · obtain ⟨h1,h2⟩ := h
      obtain ⟨t, ht⟩ := h1
      constructor
      · use t
      · contrapose! h2
        use 0; simp [h2]

  le_antisymm := le_antisymm'
  le_total := by
    intro a b
    have := trichotomous' a b
    rcases this with (h | h | h)
    · right; exact h.1
    · left; exact h.1
    · rw [h]; left; use 0; simp
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := (neg_eq_mul_neg_one _).symm

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use fun z ↦ z ≥ 0
  simp
  constructor
  · intro n hn;
    choose t ht using hn
    use t+1; simp [ht]
  · use -1;
    rw [lt_iff_exists_positive_difference]
    use 1
    constructor
    · omega
    · rw [natCast_eq, ofNat_eq, ofNat_eq,neg_eq, add_eq, eq]

/- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  choose t ht using h; simp at ht
  use t*t; simp [ht]

lemma Int.pos_iff_gt_zero (n:Int) : n.IsPos ↔ 0 < n := by
  constructor <;> intro h
  · obtain ⟨ m, hm1, hm2 ⟩ := h
    rw [lt_iff_exists_positive_difference]
    use m; simp [hm2]; omega
  · have ⟨h1,h2⟩ := h
    choose t ht using h1
    use t; simp [ht];
    simp at ht;
    suffices t ≠ 0 by omega
    contrapose! h2; simp [h2] at ht; exact ht.symm


lemma Int.neg_iff_lt_zero (n:Int) : n.IsNeg ↔ n < 0 := by
  constructor <;> intro h
  · obtain ⟨ m, hm1, hm2 ⟩ := h
    rw [lt_iff_exists_positive_difference]
    use m; simp [hm2]; omega
  · have ⟨h1,h2⟩ := h
    choose t ht using h1
    use t;
    have : 0 - t = t - t + n := by simp [ht]
    simp at this; simp [this]
    suffices t ≠ 0 by omega
    contrapose! h2; simp [h2] at ht; exact ht.symm

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases trichotomous' 0 n with (h | h | h)
  · conv at h => change n < 0
    have := h.1
    rw [← neg_iff_lt_zero] at h
    choose t ht using h
    simp [ht.2];
    have : 0 ≤ t := by omega
    have : 0 ≤ (t:Int) := by use t; simp
    apply Int.sq_nonneg_of_pos _ this
  · have := h.1
    apply Int.sq_nonneg_of_pos _ this
  · rw [← h]; simp

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have := Int.sq_nonneg n
  choose t ht using this
  use t
  simp [ht]




/- Skipping the Int API for now

/-
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro ⟨a, b⟩ ⟨c, d⟩ h; simp at *; omega)
  invFun := sorry
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry
-/


end Section_4_1
