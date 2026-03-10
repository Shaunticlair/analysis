import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

theorem abs_of_pos' {x: ℚ} (hx: 0 ≤  x) : abs x = x := by
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx <;> simp [hx]

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

theorem abs_of_neg' {x: ℚ} (hx: x ≤  0) : abs x = -x := by
  rw [le_iff_lt_or_eq] at hx
  rcases hx with hx | hx
  · exact abs_of_neg hx
  · simp [hx]

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
@[simp]
theorem abs_eq_abs (x: ℚ) : |x| = abs x  := by
  by_cases h : x > 0
  · rw [abs_of_pos h,_root_.abs_of_pos h]
  · by_cases h' : x < 0
    · rw [abs_of_neg h', _root_.abs_of_neg h']
    · have : x = 0 := by linarith
      rw [this, abs_of_zero, _root_.abs_zero]

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  rcases le_total x 0 with (h | h)
  · simp [abs_of_neg' h]; exact h
  · simp [abs_of_pos' h]; exact h

theorem abs_nonneg' (x: ℚ) : abs (x) ≥ 0 := by
  rw [← abs_eq_abs]; apply abs_nonneg

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  constructor <;> intro h1
  · rcases le_total x 0 with (h | h)
    · simp [abs_of_neg' h] at h1; exact h1
    · simp [abs_of_pos' h] at h1; exact h1
  · simp [h1];

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  rcases le_total x 0 with (h | h)
  · rw [abs_eq_abs, abs_of_neg' h]; ring_nf;
    constructor; simp;
    -- Show the method once to demonstrate that I know what's going on
    · (have : x ≤ 0 := h); (have : 0 ≤ -x := by linarith); linarith
  · simp [abs_of_pos' h]; exact h


lemma negx_le_abs (x:ℚ) : -x ≤ |x| := by have:= le_abs x; linarith

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  rcases le_total (x+y) 0 with (h | h)
  · rw [abs_eq_abs, abs_of_neg' h]; ring_nf
    linarith [negx_le_abs x, negx_le_abs y]
  · rw [abs_eq_abs, abs_of_pos' h]; ring_nf
    linarith [le_abs x, le_abs y]




/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  rcases le_total x 0 with (hx | hx)
  · simp [abs_of_neg' hx]; constructor <;> intro h
    · linarith -- Flip the sign of h.1
    · constructor
      · linarith -- Flip signs on h
      · have : 0 ≤ -x := by linarith -- x ≤ 0 ≤ -x ≤ y
        linarith
  · simp [abs_of_pos' hx]; intro h
    have : 0 ≤ y := by linarith -- 0 ≤ x ≤ y
    have : -y ≤ 0 := by linarith -- Flip sign
    linarith -- -y ≤ 0 ≤ x


/-
    The alternative for case 1 used before looked something like this (ew):
    have : (x*y) = (-x)*(-y) := by ring;
    rw [this]; (have : 0 ≤ (-x) := by linarith); have : 0 ≤ (-y) := by linarith;
    have : 0 ≤ (-x)*(-y) := by positivity;
    rw [abs_of_pos' this]
    -/

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  rcases le_total x 0 with (hx | hx) <;> rcases le_total y 0 with (hy | hy)
  · (repeat rw [abs_eq_abs]); rw [abs_of_neg' hx, abs_of_neg' hy];
    suffices (x*y) ≥ 0  by rw [abs_of_pos' this]; ring
    apply mul_nonneg_of_nonpos_of_nonpos hx hy
  · (repeat rw [abs_eq_abs]); rw [abs_of_neg' hx, abs_of_pos' hy];
    suffices (x*y) ≤ 0  by rw [abs_of_neg' this]; ring
    apply mul_nonpos_of_nonpos_of_nonneg hx hy
  · (repeat rw [abs_eq_abs]); rw [abs_of_pos' hx, abs_of_neg' hy];
    suffices (x*y) ≤ 0  by rw [abs_of_neg' this]; ring
    apply mul_nonpos_of_nonneg_of_nonpos hx hy
  · (repeat rw [abs_eq_abs]); rw [abs_of_pos' hx, abs_of_pos' hy];
    suffices (x*y) ≥ 0  by rw [abs_of_pos' this];
    apply mul_nonneg hx hy

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  have : |x * (-1)| = |x| * |-1| := abs_mul x (-1)
  rw [abs_eq_abs] at *; simp at *; exact this


/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := abs_nonneg _

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [abs_eq_zero_iff]; grind

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  unfold dist; rw [← neg_sub, abs_neg];


/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  have : (x - z) = (x - y) + (y - z) := by ring
  unfold dist; rw [this]; apply abs_add

/-
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]; norm_num; rw [abs_of_pos (by norm_num)]; norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [close_iff]; norm_num; rw [abs_of_pos (by norm_num)]; norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [close_iff]; simp; linarith

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by rw [close_iff]; simp;

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor <;> intro h
  · intro e he; rw [h]; rw [close_iff]; simp; linarith
  · contrapose! h; use |x-y|/2
    have hnng:= abs_nonneg (x-y)
    have : |x-y| > 0 := by
      suffices |x-y| ≠ 0 by apply lt_of_le_of_ne hnng this.symm
      rw [abs_ne_zero]; contrapose! h; linarith
    constructor
    · suffices |x-y| > 0 by linarith
      exact this
    · rw [close_iff]; push_neg
      linarith

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  repeat rw [close_iff]; have := dist_symm x y
  unfold dist at this; rw [this]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
    repeat rw [close_iff] at *;
    have := dist_le x y z; unfold dist at this; linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
    rw [close_iff] at *;
    have : |(x + z) - (y + w)| = |(x - y) + (z - w)| := by ring_nf
    have:= abs_add (x - y) (z - w); linarith

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
    rw [close_iff] at *;
    rw [← abs_neg] at hzw; conv at hzw => lhs; arg 1 ; simp
    have : |(x - z) - (y - w)| = |(x - y) + (w - z)| := by ring_nf
    have := abs_add (x - y) (w - z); linarith


/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by rw [close_iff] at *; linarith

theorem close_between' {e x y z w:ℚ} (hxy: e.Close x y) (hxz: e.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z)) : e.Close x w := by
  rw [close_iff] at *;
  rcases le_total w x with (h | h)
  · have : 0 ≤ x - w := by linarith;
    simp [abs_of_pos' this]
    (have : y ≤ x := by linarith); have : 0 ≤ x - y := by linarith
    simp [abs_of_pos' this] at hxy
    linarith -- x ≤ y + e ≤ x + w + e  (being close to y is more restrictive)
  · have : x-w ≤ 0 := by linarith;
    simp [abs_of_neg' this]
    (have : x ≤ z := by linarith); have : (x-z) ≤  0 := by linarith
    simp [abs_of_neg' this] at hxz
    linarith -- x ≥ z - e ≥ x - w - e  (being close to z is more restrictive)

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  rw [close_iff] at *;
  rcases hbetween with (h | h)
  · apply close_between' hxy hxz h
  · apply close_between' hxz hxy h

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
    rw [close_iff] at *;
    (have : (x * z) - (y * z) = (x - y) * z := by ring); rw [this]
    rw [abs_mul]; have := abs_nonneg z
    gcongr -- Mul |z| on both sides of hxy

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
    -- Fun fact, I actually found this proof before I found the one above.
    rw [close_iff] at *;

    have h:= abs_add (x*z - y*z) (y*z - y*w);
    have h3: x*z - y*z = (x - y) * z := by ring;
    nth_rw 2 [h3] at h; rw [abs_mul] at h
    have h4: y*z - y*w = y * (z - w) := by ring
    nth_rw 2 [h4] at h; rw [abs_mul] at h; nth_rw 6 [mul_comm] at h
    calc
      _ = |x * z - y * z + (y * z - y * w)| := by ring_nf
      _ ≤ |x - y| * |z| + |z - w| * |y|:= h
    gcongr




/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0


/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n



/-
For the sake of Chapter 5, I'm gonna write these proofs in such a way
that they apply to both the rationals and the reals.

I'll be borrowing some typeclasses from Mathlib to do so in a clean way.
Seems easy, but there was a remarkable amount of re-configuring a couple proofs
so that they are compatible with the type class.

I considered just using the Field typeclass for everything and calling it a day, but I'd rather use the weaker typeclasses if possible: keeps my proofs
more general, and prevents me from using overkill theorems that I don't
need.
-/

theorem pow_add' {G : Type*} [inst : Monoid G] (x : G) (m n : ℕ):
  x^n * x^m = x^(n+m) := by
  induction' n with n ih
  · rw [zero_add, _root_.pow_zero, one_mul];
  · rw [show n + 1 + m = (n + m) + 1 by ring]
    repeat rw [_root_.pow_succ']
    rw [← ih, mul_assoc]


theorem pow_mul' {G : Type*} [inst : Monoid G] (x : G) (m n : ℕ):
  (x^n)^m = x^(n*m) := by
  induction' m with m ih
  · rw [mul_zero, _root_.pow_zero, _root_.pow_zero];
  · rw [_root_.pow_succ]; have : n * (m + 1) = n * m + n := by ring;
    rw [this, ← pow_add', ih]


theorem mul_pow' {G : Type*} [inst : CommMonoid G] (x y : G) (n : ℕ):
  (x * y)^n = x^n * y^n := by
  induction' n with n ih
  · rw [_root_.pow_zero, _root_.pow_zero, _root_.pow_zero, one_mul];
  · rw [_root_.pow_succ, _root_.pow_succ, _root_.pow_succ, ih];
    nth_rw 2 [mul_assoc]; nth_rw 3 [← mul_assoc]
    rw [mul_comm x (y^n)]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc]


theorem pow_eq_zero' {G : Type*} [inst : MonoidWithZero G] [NoZeroDivisors G]
  (x : G) (n : ℕ) (hn : 0 < n) :
  x^n = 0 ↔ x = 0 := by
  constructor <;> intro h
  · induction' n with n ih
    · tauto
    · by_cases hn : 0 < n
      · rw [_root_.pow_succ] at h
        rw [mul_eq_zero] at h; rcases h with (h | h)
        · exact ih hn h
        · exact h
      · have : n = 0 := by linarith;
        simp [this] at h; exact h
  · have hp1 : ∃ r, n = r + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn);
    rw [hp1.choose_spec]; rw [_root_.pow_succ]; simp [h]


theorem pow_ne_zero' {G : Type*} [inst : MonoidWithZero G] [NoZeroDivisors G]
  (x : G) (n : ℕ) (hn : 0 < n) :
  x^n ≠ 0 ↔ (x ≠ 0) := by
  constructor <;> contrapose!;
  exact (pow_eq_zero' _ _ hn).2; exact (pow_eq_zero' _ _ hn).1



theorem pow_nonneg' {G : Type*} [inst : MonoidWithZero G] [Preorder G]
  [ZeroLEOneClass G] [PosMulMono G]
  {x : G} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  · rw [_root_.pow_zero]; norm_num
  · rw [_root_.pow_succ]; apply mul_nonneg ih hx



/-
Important, weird thing I learned: we need
nontriviality for Lean to infer that 0 < 1

It seems that 0 ≠ 1 isn't promised if G isn't nontrivial (doesn't just contain nothing or one object).

Lean can figure out that this type is nontrivial, but it won't check for that fact if we don't ask it to.

Once we've reminded it that this could be relevant information, it's smart
enough to then combine this knowledge with the other typeclass
instances for G, and infer that
(0:G) ≠ (1:G).

In other words: it *could* find the information we need to solve the problem, but it won't do so automatically (presumably, there are too many facts that *could* be useful, and it doesn't bother grabbing them all). So, we tell it to grab that info, and once it has that in hand, it'll figure out the rest.
-/
#check pow_pos

theorem pow_pos' {G : Type*} [inst : MonoidWithZero G] [PartialOrder G]
  [ZeroLEOneClass G] [PosMulStrictMono G]
  {x : G} (hx: x > 0) : ∀ (n : ℕ), x^n > 0 := by
  intro n; induction' n with n ih
  · nontriviality; -- G is nontrivial! This allows Lean to infer 0 < 1
    rw [_root_.pow_zero]; norm_num
  · rw [_root_.pow_succ]; apply mul_pos ih hx



theorem pow_ge_pow' {G : Type*} [MonoidWithZero G] [Preorder G] [ZeroLEOneClass G] [PosMulMono G] [MulPosMono G]
(x y:G) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  · rw [_root_.pow_zero, _root_.pow_zero];
  · rw [_root_.pow_succ, _root_.pow_succ];
    have hx:= le_trans hy hxy
    have := pow_nonneg' n hx; have := pow_nonneg' n hy
    change y^n * y ≤ x^n * x
    calc
      _ ≤ y^n * x := mul_le_mul_of_nonneg_left hxy this
      _ ≤ x^n * x := mul_le_mul_of_nonneg_right ih hx



theorem pow_gt_pow' {G : Type*} [MonoidWithZero G] [PartialOrder G] [ZeroLEOneClass G] [PosMulStrictMono G] [MulPosMono G]
(x y:G) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) :
x^n > y^n := by
  induction' n with n ih
  · contradiction
  · by_cases hn : 0 < n
    · rw [_root_.pow_succ, _root_.pow_succ]; have hx:= lt_of_le_of_lt hy hxy
      have := pow_pos' hx n; have := pow_nonneg' n hy
      suffices y * y^n  < x* x^n by gcongr
      calc
        _ ≤ x * y^n  := mul_le_mul_of_nonneg_right (le_of_lt hxy) this
        _ < x * x^n := mul_lt_mul_of_pos_left (ih hn) hx
    · have :  n = 0 := by linarith;
      rw [this]; simp; exact hxy

theorem pow_abs' {G : Type*} [inst : Ring G] [inst1 : LinearOrder G] [IsStrictOrderedRing G]
  (x : G) (n : ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  · rw [_root_.pow_zero, _root_.pow_zero]; norm_num
  · rw [_root_.pow_succ, _root_.pow_succ, _root_.abs_mul, ih]



/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := pow_add' x m n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := pow_mul' x m n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := mul_pow' x y n

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := pow_eq_zero' x n hn

theorem pow_ne_zero (x:ℚ) (n:ℕ) (hn: 0 < n)  : x^n ≠ 0 ↔ (x ≠ 0) := pow_ne_zero' x n hn

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := pow_nonneg' n hx

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := pow_pos' hx n

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 1) : x^n ≥ y^n :=
pow_ge_pow' x y n hxy (by linarith [hy])

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) :
x^n > y^n := pow_gt_pow' x y n hxy hy hn

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := pow_abs' x n


/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg'' {G : Type*} [DivisionMonoid G] (x:G) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

theorem pow_eq_zpow'' {G : Type*} [DivisionMonoid  G] (x:G) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n


theorem zpow_neg' {G : Type*} [DivisionMonoid G] (x:G) (z: ℤ ) : x^(-z) = 1/(x^z) := by
  rcases le_total z 0 with (hz | hz)
  · nth_rw 2 [show z = -(-z).toNat by simp [hz]];
    rw [zpow_neg'', ← pow_eq_zpow''];
    rw [show (-z).toNat = -z  by simp [hz]];
    simp
  · rw [show z = (z.toNat:ℤ) by simp [hz] ]
    rw [zpow_neg'', pow_eq_zpow''];

-- Exists already in Int but I don't wanna have to grab it
theorem toNat_of_nonneg {z:ℤ} (hz: z ≥ 0) : ∃ m : ℕ, z = (m:ℤ) := by
  use z.toNat; simp [hz]

theorem toNat_of_neg {z:ℤ} (hz: z < 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega

theorem toNat_of_nonpos {z:ℤ} (hz: z ≤ 0) : ∃ n : ℕ, z = -(n:ℤ) := by
  use (-z).toNat; rw [← neg_neg z]; congr; simp; omega
/-
I didn't want to figure out which coercions would be useful,
so I borrowed from https://github.com/rkirov/analysis-/

lemma cast_add (a b:ℕ): (a + b: ℕ) = (a: ℤ) + (b: ℤ) := by rfl
lemma cast_mul (a b:ℕ): (a * b: ℕ) = (a: ℤ) * (b: ℤ) := by rfl
lemma cast_sub (a b:ℕ) (h: b ≤ a): (a - b: ℕ) = (a: ℤ) - (b: ℤ) := by exact Int.ofNat_sub h
lemma cast_add_int_toNat (a:ℕ) (b:ℕ): ((a + b):ℤ) = a + (b:ℤ) := by rfl




theorem zpow_ne_zero {G : Type*} [GroupWithZero G] {x : G} (n : ℤ ) (hx : x ≠ 0 ) : x^n ≠ 0 := by
  rcases lt_trichotomy n 0 with (h | h | h)
  · rw [show n = -((-n).toNat) by omega]; rw [zpow_neg'']
    apply one_div_ne_zero
    apply _root_.pow_ne_zero
    exact hx
  · simp [h]
  · lift n to ℕ using (by linarith);
    rw [pow_eq_zpow'']; simp at h
    apply _root_.pow_ne_zero
    exact hx

#check inv_zpow

theorem inv_zpow {G : Type*} [DivisionMonoid G] (a : G) (n : ℤ) :
  a^(-n) = (a^n)⁻¹ := by rw [← one_div, zpow_neg']

#check inv_pow
theorem inv_zpow' {G : Type*} [DivisionMonoid G] (a : G) (n : ℤ) :
a^(-n) = (a⁻¹)^n := by -- Both cases: revert to a case of inv_pow
  by_cases h : n ≥ 0
  · lift n to ℕ using h; rw [zpow_neg'', one_div, ← inv_pow, pow_eq_zpow'']
  · nth_rw 2 [show n = - - n by omega ]; lift (-n) to ℕ using (by linarith) with k hk
    rw [zpow_neg', one_div]; repeat rw [pow_eq_zpow'']
    rw [inv_pow, inv_inv];

/-
This was my original approach that only worked with Field G.
Relies on commutativity, which is not given in GroupWithZero.
-/
theorem zpow_add'' {G : Type*} [Field G] (x:G) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  -- Assume n has greater magnitude (determines the sign of the sum): works by symm
  wlog hnm : |n| ≥ |m|
  · push_neg at hnm; specialize this x m n hx (by omega)
    rw [mul_comm, add_comm, this];
  obtain ⟨a, ha⟩ := Int.eq_nat_or_neg n
  -- Assume n is positive: if n is negative, then we move all terms to the opposite side of the equation, making the negative exponent positive.
  wlog han : a = n
  · push_neg at han; simp [han.symm] at ha
    specialize this x (-n) (-m) hx (by simp [hnm]) a (by omega) (by omega)
    (have hnm : -n + (- m) = -(n + m) := by ring); rw [hnm] at this
    repeat rw [zpow_neg'] at this
    field_simp [(zpow_ne_zero n hx), (zpow_ne_zero m hx), (zpow_ne_zero (n+m) hx)] at this
    exact this.symm
  -- Last split: check whether m is positive or negative
  obtain ⟨b, hb⟩ := Int.eq_nat_or_neg m
  rcases hb with rfl | rfl
  · rw [← han, pow_eq_zpow'', pow_eq_zpow'', ← _root_.pow_add, ← pow_eq_zpow''];
    congr -- Positive case: reducible to nat exponentiation
  · rw [← han] at *; -- Negative case: move to the other side, add
    rw [zpow_neg']; repeat rw [pow_eq_zpow'']; field_simp; ring_nf
    simp at hnm; rw [← cast_sub _ _ hnm]
    rw [pow_eq_zpow'', pow_add']; congr; omega

/-
Clean approach to zpow_add where we gradually build up multiplication with a
zpow element:
· first, multiplying by x,
· then multiplying by x^n (where (n : ℕ )),
· then finally multiplying by x^m (where (m : ℤ )).
-/
#check zpow_add_one₀
theorem zpow_succ {G : Type*} [GroupWithZero G] (z : ℤ) (x : G) (hx : x ≠ 0) :
  x^(z + 1) = x^z * x := by
  by_cases h : z ≥ 0
  · lift z to ℕ using h; rw [pow_eq_zpow'', ← _root_.pow_succ, ← pow_eq_zpow''];
    rw [show (z+1 :ℤ) = (z+1 :ℕ) by omega ];
  · rw [← inv_mul_eq_iff_eq_mul₀]; symm; rw [ ← mul_inv_eq_iff_eq_mul₀]
    repeat rw [← inv_zpow]
    lift (-(z+1)) to ℕ using (by linarith) with k hk
    rw [pow_eq_zpow'', ← _root_.pow_succ', ← pow_eq_zpow'']
    simp [hk]; apply zpow_ne_zero (z+1) hx;apply zpow_ne_zero z hx

theorem zpow_add_pow {G : Type*} [GroupWithZero G] (z : ℤ ) (x : G) (n : ℕ ) (hx : x ≠ 0) :
  x^(z + (n:ℤ)) = x^z * x^n := by
  induction' n with n ih
  · simp
  · simp [← add_assoc]; rw [zpow_succ, ih]
    rw [mul_assoc, _root_.pow_succ]; exact hx

#check zpow_add₀
theorem zpow_add''' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  rcases le_total m 0 with (h | h)
  · nth_rw 1 [show m = - (- m).toNat by omega];
    rw [zpow_neg', pow_eq_zpow''];
    field_simp [zpow_ne_zero (-m).toNat hx]
    rw [← zpow_add_pow]; congr; omega; exact hx
  · lift m to ℕ using h
    · rw [zpow_add_pow]; simp; exact hx

/-
Third approach: this one builds on the second approach, but also derives
commutativity of x^n and x^m.
-/
lemma zpow_mul_self_zpow_comm {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0):
  x^n * x^m = x^m * x^n := by
  wlog hn : n ≥ 0
  · push_neg at hn; specialize this x (-n) m hx (by linarith)
    field_simp [(zpow_ne_zero n hx)] at this
    nth_rw 1 [← this];
    rw [mul_assoc, ← mul_assoc]; simp [(zpow_ne_zero n hx)]
  wlog hm : m ≥ 0
  · push_neg at hm; specialize this x n (-m) hx hn (by linarith)
    field_simp [(zpow_ne_zero m hx)] at this
    nth_rw 2 [this];
    rw [mul_assoc, ← mul_assoc]; simp [(zpow_ne_zero m hx)]
  lift n to ℕ using hn; lift m to ℕ using hm;
  repeat rw [pow_eq_zpow''];
  repeat rw [← _root_.pow_add]
  congr 1; ring

theorem pow_add_zpow {G : Type*} [GroupWithZero G] (z : ℤ ) (x : G) (n : ℕ ) (hx: x ≠ 0):
  x^((n:ℤ) + z) = x^n * x^z := by
  rw [add_comm, ← pow_eq_zpow'', zpow_mul_self_zpow_comm, zpow_add_pow];
  simp; exact hx; exact hx


theorem zpow_add'''' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  by_cases h : n ≥ 0
  · lift n to ℕ using h; rw [pow_add_zpow, pow_eq_zpow'']; exact hx
  · nth_rw 1 [show n = - (- n).toNat by omega];
    rw [zpow_neg', pow_eq_zpow''];
    rw [one_div,inv_mul_eq_iff_eq_mul₀]
    rw [← pow_add_zpow]; congr; omega
    exact hx; apply _root_.pow_ne_zero _ hx


/-
Fourth approach: this method successfully solves the problem with only 3 cases!
(Technically m=0 is a case but it's trivial and doesn't require any work.)
-/
theorem zpow_add''''' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0):
  x^n * x^m = x^(n+m) := by
  wlog hnm : n + m ≥ 0 -- Invert both sides --> make sum positive
  · specialize this x (-m) (-n) hx (by omega)
    field_simp [zpow_ne_zero (n) hx, zpow_ne_zero (m) hx] at this
    rw [show -m + - n = -(n + m) by ring] at this
    symm at this
    rw [zpow_neg',one_div, mul_assoc, inv_mul_eq_iff_eq_mul₀] at this
    rw [this]; simp; apply zpow_ne_zero _ hx

  by_cases hn: m ≥ 0
  · lift m to ℕ using hn
    clear hnm
    induction' m with m ih;
    · simp
    simp; rw [← add_assoc]; repeat rw [zpow_succ]
    rw [← ih, ← mul_assoc]
    exact hx; exact hx

  · symm; rw [← mul_inv_eq_iff_eq_mul₀, ← inv_zpow];
    lift (-m) to ℕ using (by linarith) with a ha
    lift (n+m) to ℕ using (by linarith) with b hb
    repeat rw [pow_eq_zpow''];
    rw [← _root_.pow_add, ← pow_eq_zpow'']; congr; omega;
    apply zpow_ne_zero _ hx;

/-
Fifth approach: only two cases! I guess three, if you choose to separate out the
inductive base case. This matches the performance of the Mathlib proof.

This was accomplished by
1. cutting out half the space with n+m < 0
2. Inducting perpendicular to that boundary: inducting over values of n+m,
    rather than n or m individually. This meant I didn't need a separate case
    for n < 0 or m < 0: they were already accommodated.

This approach most directly mirrors the structure of the problem, based on x^(n+m).
-/

theorem zpow_add' {G : Type*} [GroupWithZero G] (x:G) (n m:ℤ) (hx: x ≠ 0):
  x^n * x^m = x^(n+m) := by
  wlog hnm : n + m ≥ 0 -- Invert both sides --> make sum positive
  · specialize this x (-m) (-n) hx (by omega)
    field_simp [zpow_ne_zero (n) hx, zpow_ne_zero (m) hx] at this
    rw [show -m + - n = -(n + m) by ring] at this
    symm at this
    rw [zpow_neg',one_div, mul_assoc, inv_mul_eq_iff_eq_mul₀] at this
    rw [this]; simp; apply zpow_ne_zero _ hx
  lift (n + m) to ℕ using hnm with y hy
  induction' y with y ih generalizing n m
  · rw [show n = -m by omega]; field_simp [zpow_ne_zero m hx]
  specialize ih n (m-1) (by simp at *; linarith)
  simp; rw [show m = (m-1) + 1 by omega]; repeat rw [zpow_succ]
  rw [← ih, mul_assoc]; exact hx; exact hx

/-
Misc stuff I never ended up using
-/

theorem neg_pow_add {G : Type*} [GroupWithZero G] (x:G) (n m:ℕ) (hx: x ≠ 0) :
  x^(-(n:ℤ)) * x^(-(m:ℤ)) = x^(-((n+m : ℕ):ℤ)) := by
  repeat rw [zpow_neg']
  field_simp
  rw [one_div, mul_assoc, ← _root_.pow_add]
  have := _root_.pow_ne_zero (m + n) hx
  convert (inv_mul_cancel₀ this).symm
  rw [← pow_eq_zpow'']; congr; omega

#check zpow_mul
#check inv_inj

/-
Back to normal stuff
-/


lemma neg_zpow_inj' {G : Type*} [DivisionMonoid G] {a b : G} {n m : ℤ} (h : a^(-n) = b^(-m)) : a^n = b^m :=
  by
    have := congr_arg (· * a^n) h
    have := congr_arg (b^m * · ) this
    simp_all


#check inv_zpow
#check inv_zpow'
theorem zpow_mul' {G : Type*} [DivisionMonoid G] (x:G) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  -- Negative cases can be generalized to positive
  -- Then, we just invoke pow_mul
  wlog hn: n ≥ 0
  · specialize this x (-n) (-m) (by omega)
    nth_rw 2 [inv_zpow] at this; rw [inv_zpow', inv_inv] at this
    simpa
  lift n to ℕ using hn
  wlog hm: m ≥ 0
  · specialize this x (-m) n (by omega)
    rw [show n * (-m) = -(n*m) by ring] at this
    simpa [neg_zpow_inj']
  lift m to ℕ using hm
  rw [← cast_mul]; repeat rw [pow_eq_zpow''];
  rw [_root_.pow_mul];

theorem pow_div' {G : Type*} [DivisionMonoid G] (x:G) (m:ℕ) : (1/x)^m = 1/(x^m) := by
  induction' m with m ih
  · rw [_root_.pow_zero, _root_.pow_zero]; norm_num
  · rw [_root_.pow_succ', _root_.pow_succ, ih];
    simp

#check mul_zpow
#check inv_inv

theorem mul_zpow' {G : Type*} [DivisionCommMonoid G] (x y:G) (n:ℤ) :
(x*y)^n = x^n * y^n := by
  wlog hn : n ≥ 0
  · specialize this x y (-n) (by omega)
    field_simp [zpow_neg'] at this
    rwa [← inv_inj, ← one_div, ← one_div]
  lift n to ℕ using hn; repeat rw [pow_eq_zpow''];
  apply mul_pow'


/-
This is basically pulled directly from Basic.lean, for practice-/
theorem inv_pos{G : Type*} [GroupWithZero G] [PartialOrder G] [PosMulReflectLT G] {a : G} :
  0 < a⁻¹ ↔ 0 < a := by
  suffices h : ∀ (x:G), 0 < x → 0 < x⁻¹ from -- The "from" keyword seems to be
    ⟨by nth_rw 2 [← inv_inv a];exact h a⁻¹, h a⟩ -- for construction instead of proof
  intro x hx
  apply lt_of_mul_lt_mul_left _ hx.le -- Also learning about .le convention, cool
  apply lt_of_mul_lt_mul_left _ hx.le -- Instead of 0 < 1, we want 0 < x
  rw [mul_inv_cancel₀ hx.ne']
  simpa

/-
This one is a little messy: it requires PosMulStrictMono to use pow_pos (which
is the obvious solution), but Lean is too dumb to infer it.

So, I used the Basic.lean approach to convert PosMulReflectLT ∧ GroupWithZero to
PosMulStrictMono.
This feels a little like cheating, but whatever. I could manually re-define the
lemma with (ostensibly but not really) weaker constraints, but that
seems like a waste of time.
-/
theorem zpow_pos' {G : Type*} [inst : GroupWithZero G] [inst_1 : PartialOrder G]
[PosMulReflectLT G] [ZeroLEOneClass G]
{x:G} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  haveI : PosMulStrictMono G := PosMulReflectLT.toPosMulStrictMono G
  rcases lt_trichotomy n 0 with (h | h | h)
  · rw [show n = - - n by omega]; rw [zpow_neg', one_div];
    rw [gt_iff_lt, inv_pos]
    lift (-n) to ℕ using (by linarith) with m hm
    rw [pow_eq_zpow'']; apply pow_pos' hx
  · simp [h]
  · lift n to ℕ using (by linarith); rw [pow_eq_zpow''];
    rw [gt_iff_lt]; apply pow_pos' hx

/-
At this point, I got into a weird insane mess realizing that only SOME VERSIONS
of pow_le_pow_left₀ require ZeroLEOneClass.

Apparently, it's because 4 months ago (today is 12/29/2025, so like August I guess),
someone modified pow_le_pow_left₀ to not require ZeroLEOneClass, by using a clever
n+2 induction.

Also zpow_le_zpow_left₀ was added 4 days ago LOL, I guess that explains why I was
confused that I couldn't find it locally.

So, for sanity's sake, I'll just use ZeroLEOneClass. Especially since pow_le_pow_left₀
uses weird induction, and I'm not currently practicing that.

Sure did learn a lot, though.
-/

#check pow_le_pow_left₀

-- Used to infer desired typeclass instances (borrowed from Basic.lean)
attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  PosMulReflectLT.toPosMulReflectLE PosMulReflectLT.toMulPosReflectLT
  MulPosReflectLT.toMulPosReflectLE


theorem zpow_ge_zpow' {G : Type*} [GroupWithZero G] [PartialOrder G]
[PosMulReflectLT G] [MulPosMono G] [ZeroLEOneClass G]
{x y : G} {n : ℤ} (hxy : x ≥ y) (hy : y > 0) (hn : n > 0) : x^n ≥ y^n := by
  lift n to ℕ using (by linarith)
  repeat rw [pow_eq_zpow''];
  apply pow_ge_pow' _ _ _ hxy hy.le

/-
This theorem doesn't seem to have an exact match in mathlib
I wasn't sure exactly how much I need, so I just added the instance I
immediately wanted: MulPosReflectLT.
-/

theorem zpow_ge_zpow_ofneg' {G : Type*} [GroupWithZero G] [PartialOrder G]
[PosMulReflectLT G] [MulPosReflectLT G] [MulPosMono G] [ZeroLEOneClass G]
{x y : G} {n : ℤ} (hxy : x ≥ y) (hy : y > 0) (hn : n < 0) : x^n ≤ y^n := by
  refine le_of_mul_le_mul_left ?_ (zpow_pos' (-n) hy) -- Move y^m to the other side
  rw [zpow_add'];
  have : x > 0 := lt_of_lt_of_le hy hxy
  refine le_of_mul_le_mul_right ?_ (zpow_pos' (-n) this) -- Move x^m to the other side
  rw [mul_assoc, zpow_add' ];
  simp [-_root_.zpow_neg] -- Cancel out terms
  apply zpow_ge_zpow' hxy hy (by linarith)
  exact this.ne'; exact hy.ne'

-- Another indirect victim of removing [ZeroLEOneClass G]
-- I'll just add it back in; I don't wanna deal with the current proof, relies on
-- similar n+2 cleverness.

theorem pow_inj' {G : Type*} [MonoidWithZero G] [LinearOrder G] [PosMulStrictMono G] [ZeroLEOneClass G]
{x y : G} {n : ℕ} [MulPosMono G] (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) :
x = y := by
  rcases lt_trichotomy x y with (h | h | h)
  · have := pow_gt_pow' y x n h (le_of_lt hx) (by omega);
    have := ne_of_gt this; symm at this; contradiction
  · exact h
  · have := pow_gt_pow' x y n h (le_of_lt hy) (by omega);
    have := ne_of_gt this; contradiction

theorem zpow_inj' {G : Type*} [GroupWithZero G] [LinearOrder G] [PosMulStrictMono G] [ZeroLEOneClass G]
{x y : G} {n : ℤ} [MulPosMono G] (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n)
: x = y := by
  wlog hnp: n > 0
  · have hn': -n > 0 := by omega;
    refine this hx hy hn'.ne' ?_ hn'
    repeat rw [zpow_neg'];
    rw [hxy]
  lift n to ℕ using (by linarith); repeat rw [pow_eq_zpow''] at hxy
  apply pow_inj' hx hy (by linarith) hxy

lemma abs_one_div' {G : Type*} [Field G] [LinearOrder G] [IsStrictOrderedRing G] (a : G) :
|1 / a| = 1 / |a| := by
  rcases le_total a 0 with (ha0 | ha0)
  · rw [abs_of_nonpos (one_div_nonpos.mpr ha0), abs_of_nonpos ha0]; ring
  · rw [abs_of_nonneg (one_div_nonneg.mpr ha0), abs_of_nonneg ha0];

/-
Mathlib uses abs_zpow, which has the same constraints as abs_one_div. So,
we use the same typeclasses here.
-/

theorem zpow_abs' {G : Type*} [Field G] [LinearOrder G] [IsStrictOrderedRing G] (x : G) (n : ℤ) : |x|^n = |x^n| := by
  wlog hn0 : n ≥ 0
  · push_neg at hn0; obtain ⟨m, hm⟩ := toNat_of_neg (by omega); subst hm
    rw [zpow_neg', zpow_neg', this x m (by omega), abs_one_div']
  obtain ⟨m, hm⟩ := toNat_of_nonneg hn0; subst hm; repeat rw [pow_eq_zpow''];
  apply pow_abs'


/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x : ℚ) (n m : ℤ ) (hx: x ≠ 0): x^n * x^m = x^(n + m) := zpow_add' x n m hx

lemma pow_div (x : ℚ ) (m : ℕ ): (1/x)^m = 1/(x^m) := pow_div' x m

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := zpow_mul' x n m

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := mul_zpow' x y n

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := zpow_pos' n hx

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0):
x^n ≥ y^n := zpow_ge_zpow' hxy hy hn



theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0)
: x^n ≤ y^n := zpow_ge_zpow_ofneg' hxy hy hn

theorem pow_inj {x y:ℚ} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n)
: x = y := pow_inj' hx hy hn hxy

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n)
: x = y := zpow_inj' hx hy hn hxy

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := zpow_abs' x n


/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  induction' N with N ih
  · norm_num;
  · rw [Nat.pow_succ];
    by_cases hn : N ≥ 1
    · suffices 2*N ≥ N + 1 by linarith
      linarith
    · have : N = 0 := by linarith;
      subst this; rw [Nat.pow_zero, Nat.one_mul, Nat.zero_add]; norm_num
