import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of ℕ and ℤ.

- Equivalence with the Mathlib rationals `_root_.Rat` (or `ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers `ℕ` and integers `ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by
      intro rat; rfl
    symm := by
      intro rat1 rat2 hrat; rw [hrat]
    trans := by
      intro a b c hab hbc
      let a1 := a.numerator
      let a2 := a.denominator
      let b1 := b.numerator
      let b2 := b.denominator
      let c1 := c.numerator
      let c2 := c.denominator
      suffices a1*c2 * b2  = c1*a2 * b2 by
          have h:= b.nonzero; apply mul_right_cancel₀ h this
      suffices c2 * (a1 * b2) = a2 * (c1 * b2) by linarith
      rw [hab, ← hbc]; linarith
    }


@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b, hb ⟩ ⟨ c,d, hd ⟩
    simp [Setoid.r]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by sorry)

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ h3
    simp_all [Setoid.r])

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  simp [coe_Nat_eq, coe_Nat_eq, of_Nat_eq, add_eq]


/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  simp [coe_Int_eq, coe_Int_eq, coe_Int_eq, add_eq]

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  simp [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq]

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

@[simp]
theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro z1 z2 h; simp at h;
  rw [coe_Int_eq, coe_Int_eq, eq] at h
  simp at h; exact h; decide; decide

/-
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ h3
    simp_all [Setoid.r]
    by_cases ha : a = 0
    · simp_all -- Junk case: a=0, then c=0, so both sides are junk (0//1)
    · simp [ha]
      have hc : c ≠ 0 := by -- If c=0, then ad=0, so a=0 or d=0, both wrong
        by_contra hc; simp [hc] at h3; simp_all
      simp [hc]; linarith -- We end up with ad=cb, which is known by rat equality
      -- Since inverse just flips the equation, we end up with the commuted ver
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by
  intro a;
  obtain ⟨ a1, a2, h, rfl⟩ := eq_diff a
  rw [of_Nat_eq, add_eq]; simp; decide; exact h)
 (by
  intro a;
  obtain ⟨ a1, a2, h, rfl⟩ := eq_diff a
  rw [neg_eq, add_eq, of_Nat_eq, eq];
  ring; simp [h]; decide; repeat exact h;
 )

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro x y
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    rw [add_eq, add_eq]; ring_nf; repeat simp_all

@[simp]
lemma Rat.zero_num_invariant {a b:ℤ} (ha : a ≠ 0) (hb: b ≠ 0) :
(0//a : Rat) = (0//b : Rat) := by
  rw [eq]; repeat simp_all

/-
∀ (a b : Rat), a * b = b * a
-/
lemma Rat.mul_comm' (x y:Rat) : x * y = y * x := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  rw [mul_eq, mul_eq]; ring_nf; repeat simp_all

lemma Rat.one_mul' (x:Rat) : 1 * x = x := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  rw [of_Nat_eq, mul_eq]; simp; decide; exact hb

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := mul_comm'
  mul_assoc := by
    intro x y z
    obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
    rw [mul_eq, mul_eq, mul_eq, mul_eq]
    ring_nf; repeat simp_all
  one_mul := one_mul'

  mul_one := by
    intro x; rw [mul_comm', one_mul']

-- ∀ (a b c : Rat), a * (b + c) = a * b + a * c
lemma Rat.left_distrib' (a b c : Rat) : a * (b + c) = a * b + a * c := by
  obtain ⟨ a1, a2, ha2, rfl ⟩ := eq_diff a
  obtain ⟨ b1, b2, hb2, rfl ⟩ := eq_diff b
  obtain ⟨ c1, c2, hc2, rfl ⟩ := eq_diff c
  rw [add_eq, mul_eq, mul_eq, mul_eq, add_eq, eq];
  ring
  repeat simp_all

lemma Rat.zero_mul' (x:Rat) : 0 * x = 0 := by
  obtain ⟨ a1, a2, ha2, rfl ⟩ := eq_diff x
  rw [of_Nat_eq, mul_eq]; ring_nf;
  apply zero_num_invariant; exact ha2; decide; decide; exact ha2

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := left_distrib'
  right_distrib := by intro a b c;
                      rw [mul_comm, left_distrib', mul_comm a c, mul_comm b c]
  zero_mul := zero_mul'
  mul_zero := by intro x; rw [mul_comm, zero_mul']
  mul_assoc := mul_assoc
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro q1 q2 h
  simp at h;
  -- Nonzero denominators
  have h1 : q1.den ≠ 0 := Rat.den_nz q1
  have h2 : q2.den ≠ 0 := Rat.den_nz q2
  conv at h => change (q1.num // q1.den : Rat) = (q2.num // q2.den : Rat)
  rw [eq] at h;
  rw [Rat.eq_iff_mul_eq_mul]
  exact h
  repeat simp

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

lemma Rat.div_int_eq (a b : ℤ) (hb : b ≠ 0) :  (a // b) = (a / b) := by
  rw [div_eq, coe_Int_eq, coe_Int_eq, inv_eq, mul_eq, eq ]; repeat simp_all


lemma Rat.zero_iff_num_zero (qnum qden:ℤ) (hden: qden ≠ 0) :
  (qnum // qden = 0) ↔ qnum = 0 := by
  constructor <;> intro h
  · rw [of_Nat_eq, eq] at h; simp at h; exact h; exact hden; decide
  · rw [of_Nat_eq, eq]; simp; exact h; exact hden; decide

-- Contrapositive equivalence
lemma Rat.zero_iff_num_zero' (qnum qden:ℤ) (hden: qden ≠ 0) :
  (qnum // qden ≠ 0) ↔ qnum ≠ 0 := by
  constructor <;> intro h
  · contrapose! h; revert h; apply (zero_iff_num_zero _ _ hden ).2
  · contrapose! h; revert h; apply (zero_iff_num_zero _ _ hden ).1

lemma Rat.mul_inv_cancel' (a : Rat) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨ a1, a2, ha2, rfl ⟩ := eq_diff a
  have ha1 : a1 ≠ 0 := (Rat.zero_iff_num_zero' a1 a2 ha2).mp ha
  rw [inv_eq, mul_eq, of_Nat_eq, eq]; simp; linarith
  simp [ha1, ha2]; repeat simp_all


/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    use 0, 1; simp;rw [of_Nat_eq, of_Nat_eq, eq]; repeat simp
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
  rw [Rat.div_eq, Rat.inv_eq, Rat.mul_eq, Rat.eq]; ring; repeat decide

/-
  Embedding the integers in the rationals is a ring homomorphism.

  We already proved these homomorphic properties above.
-/
def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intro x y; rw [intCast_add]
  map_mul' := by intro x y; rw [intCast_mul]

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r



/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  by_cases ha0 : a = 0
  · left; rw [of_Nat_eq, eq]; simp [ha0]; repeat simp_all
  right
  by_cases ha : a > 0 <;> by_cases hb0 : b > 0
  · left; use a, b; simp_all; apply div_int_eq; apply hb
  · right; use (a/(-b)); constructor; use a, (-b); simp [ha]; omega
    have : -b ≠ 0 := by omega
    rw [intCast_neg, ← div_int_eq, neg_eq, eq]; repeat simp_all
  · right; use (-a/b); constructor; use (-a), b; simp [hb0]; omega
    rw [intCast_neg, ← div_int_eq, neg_eq, eq]; repeat simp_all
  · left; use -a, -b;
    have : -a > 0 := by omega;
    have : -b > 0 := by omega;
    simp_all; apply div_int_eq _ _ hb

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  by_contra h; obtain ⟨ h1, h2 ⟩ := h;
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h2
  rw [← div_int_eq] at h1;
  rw [of_Nat_eq, eq] at h1; simp at h1
  repeat omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  by_contra h; obtain ⟨ h1, h2 ⟩ := h;
  obtain ⟨ r, h3, rfl ⟩ := h2;
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h3
  rw [← div_int_eq] at h1;
  rw [of_Nat_eq, neg_eq, eq] at h1; simp at h1
  repeat omega

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  by_contra h; obtain ⟨ h1, h2 ⟩ := h;
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h1;
  obtain ⟨ r, h3, h4 ⟩ := h2;
  obtain ⟨ c, d, hc, hd, rfl ⟩ := h3;
  repeat rw [← div_int_eq] at h4;
  rw [neg_eq, eq] at h4;
  have had: a*d > 0 := by clear h4; apply Int.mul_pos; apply ha; apply hd
  have hcb: c*b > 0 := by clear h4; positivity
  linarith
  repeat omega
/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

lemma Rat.isPos_iff_neg_isNeg (x:Rat) : x.isPos ↔ (-x).isNeg := by
  constructor <;> intro h
  · obtain ⟨ a, b, ha, hb, rfl ⟩ := h
    use a/b; constructor; use a, b; rfl
  · obtain ⟨ r, h1, h2 ⟩ := h; simp at h2
    rw [h2]; assumption

lemma Rat.isNeg_iff_neg_isPos (x:Rat) : x.isNeg ↔ (-x).isPos := by
  constructor <;> intro h
  · obtain ⟨ r, h1, h2 ⟩ := h;
    rw [h2]; simp; assumption
  · obtain ⟨ a, b, ha, hb, h ⟩ := h
    use a/b; constructor; use a, b; simp [← h]

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  change y < x ↔ (x-y).isPos
  rw [lt_iff]
  have : y - x = -(x - y) := by ring
  rw [this]; symm; apply isPos_iff_neg_isNeg

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  change y ≤ x ↔ (y < x) ∨ (x = y)
  rw [eq_comm]
  apply le_iff y x

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rcases Rat.trichotomous (x - y) with (h | h | h)
  · right; right; apply sub_eq_zero.mp h
  · left; rw [gt_iff]; exact h
  · right; left; rw [lt_iff]; exact h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]; apply Rat.not_pos_and_neg

lemma Rat.dist_zero (x y : Rat):  x = y ↔ x - y = 0 := by
  constructor <;> intro h
  · rw [h]; ring
  · apply sub_eq_zero.mp h

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, dist_zero, and_comm]
  apply Rat.not_zero_and_pos


/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, dist_zero, and_comm]
  apply Rat.not_zero_and_neg

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ (y - x).isPos := by
  rw [lt_iff, isPos_iff_neg_isNeg]; simp

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  simp [lt_iff, isNeg_iff_neg_isPos] at *
  obtain ⟨ a1, b1, ha1, hb1, hxy ⟩ := hxy
  obtain ⟨ a2, b2, ha2, hb2, hyz ⟩ := hyz
  have : z - x = (y - x) + (z - y) := by ring
  rw [this, hxy, hyz]
  rw [← div_int_eq, ← div_int_eq, add_eq]
  use a1*b2 + b1*a2, b1*b2; simp
  constructor; positivity; constructor; positivity;
  rw [div_int_eq]; simp_all
  have : b1 * b2 > 0 := by positivity
  repeat omega

-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff] at *; simp [hxy]

lemma Rat.pos_times_pos {a b: Rat} (ha: isPos a) (hb: isPos b) : isPos (a * b) := by
  obtain ⟨ a1, a2, ha1, ha2, rfl ⟩ := ha
  obtain ⟨ b1, b2, hb1, hb2, rfl ⟩ := hb
  rw [← div_int_eq, ← div_int_eq, mul_eq]
  use a1*b1, a2*b2; simp
  constructor; positivity; constructor; positivity
  rw [div_int_eq]; simp_all;
  have : a2 * b2 > 0 := by positivity
  repeat omega

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  rw [lt_iff, isNeg_iff_neg_isPos] at *;
  have : (x - y) * z = (x * z) - (y * z) := by ring  -- It's just distributivity
  rw [← this];
  have : (-((x - y) * z)) = ((-(x - y)) * z) := by ring
  rw [this]
  apply pos_times_pos hxy hz


lemma Rat.sub_eq {a b : Rat} : a - b = a + (-b) := by rfl


lemma Rat.mk_eq_formalDiv (a b : ℤ) (hb : b ≠ 0) :
    (⟦{ numerator := a, denominator := b, nonzero := hb }⟧ : Rat) = a // b := by
  simp only [formalDiv]
  simp [hb]

lemma Rat.div_neg (a b : Rat) : a / (-b) = -(a / b) := by
  rw [div_eq, div_eq]; ring

lemma Rat.neg_div (a b : Rat) : (-a)/b = -(a / b) := by
  rw [div_eq, div_eq]; ring



lemma Rat.neg_sub (a b : Rat) : -(a - b) = b - a := by
  rw [sub_eq, sub_eq]; ring


instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  simp
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            rw [ mk_eq_formalDiv, mk_eq_formalDiv]
            rw [le_iff, lt_iff, isNeg, eq]
            rcases lt_or_eq_of_le h with (h | h)
            · left; rw [sub_eq, neg_eq, add_eq]
              use (b*c - a*d)/(b*d)
              constructor ; use (b*c - a*d), (b*d)
              constructor; apply Int.sub_pos_of_lt h
              constructor; positivity; simp
              rw [div_int_eq]; simp; ring
              have : b * d > 0 := by positivity
              repeat omega
            · right; rw [h]; ring
            exact hb; exact hd
          | isFalse h =>
            apply isFalse;
            rw [le_iff]; push_neg
            simp [Setoid.r]
            constructor
            · simp at h; rw [lt_iff, isNeg]; push_neg
              rw [ mk_eq_formalDiv, mk_eq_formalDiv]
              intro r rpos; rw [sub_eq, neg_eq, add_eq]
              have : (a*d + b *(-c)) = a*d - b*c := by ring
              rw [this]

              have : ((a * d - b * c) // (b * d) ).isPos := by
                use (a*d - b*c), (b*d)
                constructor; apply Int.sub_pos_of_lt h
                constructor; positivity;
                rw [← div_int_eq]; simp_all
              have hcontra: (-r).isNeg := (isPos_iff_neg_isNeg _ ).1 rpos
              intro hr; rw [← hr] at hcontra
              apply Rat.not_pos_and_neg; apply And.intro this hcontra
              repeat simp_all
            · linarith
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [le_iff, lt_iff, isNeg, sub_eq]; simp [Setoid.r]
            rw [ mk_eq_formalDiv, mk_eq_formalDiv, neg_eq, add_eq]
            rcases lt_or_eq_of_le h with (h | h)
            · left; use -((a*d - b*c )/(b*d))
              simp
              constructor
              · use (a*d-b*c), (-b*d)
                constructor; apply Int.sub_pos_of_lt h
                constructor; push_neg at hbd; linarith
                simp; rw [div_neg]
              · rw [div_int_eq]; congr 1; simp; ring; omega
            · right; rw [← h]; ring
            repeat simp_all
          | isFalse h =>
            apply isFalse
            rw [le_iff]; push_neg
            simp [Setoid.r]
            constructor
            · simp at h; rw [lt_iff, isNeg]; push_neg
              rw [mk_eq_formalDiv, mk_eq_formalDiv]
              intro r rpos; rw [sub_eq, neg_eq, add_eq]
              have : (a*d + b *(-c)) = a*d - b*c := by ring
              rw [this]

              have : ((a * d - b * c) // (b * d) ).isPos := by
                use (b*c - a*d), (-b*d)
                constructor; apply Int.sub_pos_of_lt h
                constructor; push_neg at hbd; linarith
                rw [div_int_eq]; simp; ring;
                simp at hbd; linarith

              have hcontra: (-r).isNeg := (isPos_iff_neg_isNeg _).1 rpos
              intro hr; rw [← hr] at hcontra
              apply Rat.not_pos_and_neg; apply And.intro this hcontra
              repeat simp_all
            · linarith

  exact Quotient.recOnSubsingleton₂ n m this

lemma Rat.lt_iff' (x y:Rat) : x < y ↔ ∃ z, z.isPos ∧ x + z = y := by
  rw [lt_iff]
  constructor <;> intro h
  · use (y-x); constructor;
    · rw [← neg_sub]; rw [isNeg_iff_neg_isPos] at h; exact h
    · ring
  · obtain ⟨ z, hpz, hz ⟩ := h; rw [isNeg_iff_neg_isPos]
    have : z =-(x-y) := by rw [← hz]; ring
    rw [← this]; exact hpz

lemma Rat.le_iff' (x y:Rat) : x ≤ y ↔ ∃ z, ¬ (z.isNeg) ∧ x + z = y := by
  constructor <;> intro h
  · rw [le_iff] at h
    rcases h with (h | h)
    · rw [lt_iff'] at h; obtain ⟨ z, hpz, hz ⟩ := h;
      use z; constructor; intro hneg;
      apply Rat.not_pos_and_neg _ ⟨ hpz, hneg⟩; exact hz
    · use y-x; simp; symm at h; rw [dist_zero] at h;
      intro h'; apply not_zero_and_neg _ ⟨h, h'⟩
  · obtain ⟨ z, hnz, hz ⟩ := h; rw [le_iff]
    rcases Rat.trichotomous z with (h | h | h)
    · right; simp [h] at hz; exact hz
    · left; rw [lt_iff']; use z
    · contradiction

lemma Rat.not_isNeg (z : Rat): ¬(z.isNeg) ↔ ∃ (a b : ℤ), a ≥ 0 ∧ b > 0 ∧ z = a/b := by
  constructor <;> intro h
  · by_cases hz : z = 0
    · use 0, 1; simp [hz];
    · rcases Rat.trichotomous z with (h | h | h)
      · contradiction
      · obtain ⟨ a, b, ha, hb, rfl ⟩ := h; use a, b; simp_all; omega;
      · contradiction
  · obtain ⟨ a, b, ha, hb, rfl ⟩ := h
    rcases lt_or_eq_of_le ha with (ha | ha)
    · intro h; apply Rat.not_pos_and_neg; refine And.intro ?_ h; use a, b;
    · intro h; apply Rat.not_zero_and_neg; refine And.intro ?_ h;
      rw [← div_int_eq, ← ha, of_Nat_eq, eq]; repeat simp_all;
      simp [← ha]; repeat simp_all; omega

-- Honestly, it feels like there should've been a less tedious way to do this.

--Contrapose of Rat.coe_Int_inj
@[simp]
lemma Rat.coe_Int_inj_mt :  ∀ {a b : ℤ},  ¬ a = b → ¬ (a : Rat) = b  := by
  intros a b h; contrapose! h; apply Rat.coe_Int_inj; exact h

-- Version where you use an ofnat for one of the ints is a natlit
@[simp]
lemma Rat.coe_Int_mt' {a:ℤ} {b:ℕ} :  ¬ a = ofNat(b) → ¬ (a : Rat) = ofNat(b) := by
  intros h; contrapose! h; apply Rat.coe_Int_inj; exact h

lemma Rat.lt_iff_isNeg (x : ℤ ): x < 0 ↔ (x : Rat).isNeg := by
  constructor <;> intro h
  · rw [isNeg_iff_neg_isPos]; use -x, 1; simp [h]
  · rw [isNeg_iff_neg_isPos] at h;  suffices -x > 0 by omega
    rw [coe_Int_eq] at h; obtain ⟨ a, b, ha, hb, h ⟩ := h
    rw [neg_eq, ← div_int_eq, eq, mul_one] at h; rw [← h] at ha;
    change 0 < -x; rw [mul_comm] at ha
    apply Int.pos_of_mul_pos_right ha; repeat omega

-- Made an alternate version that I like more because it feels more natural.
-- I also made it dense because I don't like scrolling forever to get past it.
-- Probably a waste of time, but I had fun.
instance Rat.decidableRel' : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  simp
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue; rw [ mk_eq_formalDiv, mk_eq_formalDiv, le_iff']
            obtain ⟨k, hk1, hk2⟩ := le_iff_exists_nonneg_add.mp h
            use k/((b*d):ℤ ); constructor
            · rw [not_isNeg]; use k; use (b*d:ℤ)
              constructor; omega; constructor; positivity; rfl
            · rw [← div_int_eq]; rw [add_eq]; rw [eq]
              have : c * (b * (b * d)) = (b*c) * (b * d) := by ring;
              rw [this, ← hk2]; ring; repeat positivity

          | isFalse h =>
            apply isFalse; rw [ mk_eq_formalDiv, mk_eq_formalDiv]
            rw [le_iff']; by_contra hdiv; push_neg at h
            obtain ⟨ r, hrpos, hr ⟩ := hdiv; apply hrpos
            have : r = (c//d) - (a//b) := by rw [← hr]; ring
            rw [sub_eq, neg_eq, add_eq] at this; rw [this]
            rw [div_int_eq, isNeg_iff_neg_isPos, ← neg_div]; simp
            use (d*a-c*b), (b*d); constructor; linarith
            constructor; positivity; simp; ring; repeat simp_all

      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [mk_eq_formalDiv, mk_eq_formalDiv, le_iff']
            obtain ⟨k, hk1, hk2⟩ := le_iff_exists_nonneg_add.mp h
            use k/(-(b*d):ℤ); constructor
            · rw [not_isNeg]; use k; use (-(b*d):ℤ)
              constructor; omega; constructor; push_neg at hbd; omega; rfl
            · rw [← div_int_eq, add_eq, eq]; simp
              have : a * (b * d) = (a* d) * b := by ring
              rw [this, ← hk2]; ring; repeat simp_all

          | isFalse h =>
            apply isFalse
            rw [mk_eq_formalDiv, mk_eq_formalDiv, le_iff']; by_contra hdiv; push_neg at h
            obtain ⟨ r, hrpos, hr ⟩ := hdiv; apply hrpos
            have : r = (c//d) - (a//b) := by rw [← hr]; ring
            rw [sub_eq, neg_eq, add_eq] at this; rw [this]
            rw [div_int_eq, isNeg_iff_neg_isPos, ← neg_div]; simp
            use (c*b-d*a), (-(b*d)); constructor; linarith
            constructor; push_neg at hbd; linarith; simp; ring; repeat simp_all

  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := by
    intro a; right; rfl
  le_trans := by
    intro a b c hab hbc; rw [le_iff'] at *
    obtain ⟨ x, hnx, h1 ⟩ := hab; obtain ⟨ y, hny, h2 ⟩ := hbc
    use (x + y); rw [not_isNeg] at *; constructor
    · obtain ⟨ a1, b1, ha1, hb1, rfl ⟩ := hnx
      obtain ⟨ a2, b2, ha2, hb2, rfl ⟩ := hny
      use (a1*b2 + a2*b1), (b1*b2);
      constructor; positivity; constructor; positivity;
      repeat rw [← div_int_eq];
      rw [add_eq]; nth_rw 2 [mul_comm]
      repeat ((have hb12: b1*b2 > 0 := by positivity); repeat omega)
    · rw [← h2, ← h1]; ring
  lt_iff_le_not_ge := by
    intro a b;
    constructor <;> intro h1
    · constructor;
      · left; exact h1
      · rw [le_iff]; push_neg
        constructor <;> intro h2;
        · apply not_gt_and_lt _ _ ⟨h2, h1⟩
        · apply Rat.not_lt_and_eq _ _ ⟨h1, h2.symm⟩
    · rcases Rat.trichotomous' b a with (h | h | h)
      · omega
      · have : b ≤ a := by left; exact h
        exfalso; simp_all
      · have : b ≤ a := by right; exact h
        exfalso; simp_all

  le_antisymm := by
    intro a b hab hba; rw [le_iff] at *;
    rcases hab with (hab | hab) <;> rcases hba with (hba | hba)
    · exfalso; apply not_gt_and_lt; exact ⟨hab, hba⟩
    · exact hba.symm
    · exact hab
    · exact hab

  le_total := by
    intro a b;
    rcases Rat.trichotomous' a b with (h | h | h)
    · right; left; omega
    · left; left; exact h
    · right; right; exact h.symm
  toDecidableLE := decidableRel

lemma Rat.pos_iff_gt_zero (n:Rat) : n.isPos ↔ 0 < n := by
  constructor <;> intro h
  · simp [lt_iff,isNeg_iff_neg_isPos,h]
  · simp [lt_iff,isNeg_iff_neg_isPos] at h; exact h

lemma Rat.add_le_add_right' (a b : Rat) (hab : a ≤ b) (c : Rat) :
a + c ≤ b + c := by
  rw [le_iff] at hab
  rcases hab with (hab | hab)
  · left; apply add_lt_add_right _ hab
  · rw [hab]

lemma Rat.add_le_add_left' (a b : Rat) (hab : a ≤ b) (c : Rat) :
c + a ≤ c + b := by rw [add_comm c a, add_comm c b];
                    apply Rat.add_le_add_right' a b hab c

lemma Rat.mul_lt_mul_right' (x y z:Rat) (hxy: x < y) (hz: 0 < z) : x * z < y * z := by
  rw [← pos_iff_gt_zero] at hz; apply Rat.mul_lt_mul_right hxy hz

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by intro a b hab c; rw [add_comm c a, add_comm c b];
                        apply add_le_add_right' a b hab c
  add_le_add_right := add_le_add_right'
  mul_lt_mul_of_pos_left := by intro a b c hab hc; rw [mul_comm, mul_comm c b];
                               apply mul_lt_mul_right' a b c hab hc
  mul_lt_mul_of_pos_right := mul_lt_mul_right'
  le_of_add_le_add_left := by
    intro a b c h; have := add_le_add_left' (a+b) (a+c) h (-a)
    simp at this; exact this
  zero_le_one := by rw [le_iff']; use 1; rw [not_isNeg];
                    constructor; (use 1, 1; simp) ; (simp)

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) :
x * z > y * z := by
  rw [isNeg_iff_neg_isPos] at hz; change y*z < x*z; rw [lt_iff'] at *
  choose u hu using hxy; use u * (-z)
  constructor
  · apply pos_times_pos hu.1 hz
  · rw [← hu.2]; ring


-- Skipping the Rat API for now
/-
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    sorry)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := sorry
  right_inv n := sorry

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm


end Section_4_2
