import Mathlib.Tactic
import Analysis.Section_5_5

set_option linter.unusedVariables false

/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := Section_4_3.pow_add' x m n


/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := Section_4_3.pow_mul' x m n

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := Section_4_3.mul_pow' x y n

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := Section_4_3.pow_eq_zero' x n hn

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := Section_4_3.pow_nonneg' n hx

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := Section_4_3.pow_pos' hx n

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := Section_4_3.pow_ge_pow' x y n hxy hy

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := Section_4_3.pow_gt_pow' x y n hxy hy hn

theorem Real.pow_ge_pow_converse (x y:Real) (n:ℕ) (hxy: x^n ≥ y^n) (hx: x ≥ 0) (hn: n > 0) : x ≥ y := by
  contrapose! hxy; apply pow_gt_pow y x n hxy hx hn

theorem Real.pow_gt_pow_converse (x y:Real) (n:ℕ) (hxy: x^n > y^n) (hx: x ≥ 0) (hn: n > 0) : x > y := by
  contrapose! hxy; apply pow_ge_pow y x n hxy hx

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := Section_4_3.pow_abs' x n

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := Section_4_3.zpow_add' x n m hx

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := Section_4_3.zpow_mul' x n m

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := Section_4_3.mul_zpow' x y n

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := Section_4_3.zpow_pos' n hx

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := Section_4_3.zpow_ge_zpow' hxy hy hn

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := Section_4_3.zpow_ge_zpow_ofneg' hxy hy hn

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := Section_4_3.zpow_inj' hx hy hn hxy

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := Section_4_3.zpow_abs' x n

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.rootset (x:Real) (n:ℕ) : Set Real := { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup (rootset x n)

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0; simp at *; convert hx; simp; linarith

theorem le_self_pow₀' {G : Type*} [MonoidWithZero G] [Preorder G] [ZeroLEOneClass G]
  [PosMulMono G] {a : G} {n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  clear hn -- Unnecessary premise
  induction' n with n ih
  · simp
  · rw [pow_succ']
    nth_rw 1 [← mul_one a]
    exact mul_le_mul_of_nonneg_left (le_trans ha ih) (le_trans zero_le_one ha)

/-
Notably, this suggests the root of x < 0 is just 0. Why not, I guess.
-/
theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  · use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      rw [← gt_iff_lt]; convert Real.pow_gt_pow y 1 n hy' (by linarith) hn
      ring
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    apply lt_of_lt_of_le hy'
    apply le_self_pow₀' (by linarith) (by linarith)
  linarith

/-
Since it is nonempty and bounded above, we know a Real least upper bound
exists: the Sup (or in particular, the root).
-/

lemma Real.root_LUB_rootset {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
IsLUB (rootset x n) (x.root n) :=
  ExtendedReal.sSup_of_bounded (Real.rootset_nonempty hx n hn) (Real.rootset_bddAbove n hn)

/-
Next, we will be saying that (x.root n)^n = x. This is like our previous
proof that (sqrt 2)^2 = 2. So, we can use exactly the same proof structure.
-/

/-
First, we'll extract and generalize the proofs about bounding (y+ε)^n and (y-ε)^n in terms of y^n+Cε.
This will allow us to show that (x.root n)^n is neither above nor below x.
-/

lemma Real.linear_upper_bound_of_pow (y: Real) (n : ℕ) (hy : y ≥ 0) (hn : n ≠ 0):
∃ C > 0, ∀(ε : Real), ε ≥ 0 → ε ≤ 1 → (y+ε)^n ≤ y^n + C * ε := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp at *
  induction' k with k ih
  · use 1; simp
  choose C hC1 hC2 using ih
  use C + C*y + (y^(k+1))
  refine ⟨by nlinarith [Real.pow_nonneg (k+1) hy],?_⟩
  intro e he0 he1; specialize hC2 e he0 he1
  rw [pow_succ'];
  calc
    _ ≤ (y+e) * (y^(k+1) + C * e) := by gcongr
    _ = y* (y^(k+1) + C * e) + e*y^(k+1) + C*(e*e) := by ring_nf
    _ ≤ y* (y^(k+1) + C * e) + e*y^(k+1) + C*e := by gcongr; nlinarith
    _ = _ := by ring_nf;

lemma Real.linear_lower_bound_of_pow (y: Real) (n : ℕ) (hy : y ≥ 0) (hn : n ≠ 0):
∃ C > 0, ∀(ε : Real), ε ≥ 0 → ε ≤ y → (y - ε)^n ≥ y^n - C * ε := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [show k.succ = k + 1 by aesop] at *
  induction' k with k ih
  · use 1; simp
  choose C hC1 hC2 using ih (by linarith)
  use C + C*y + y^(k+1)
  refine ⟨by nlinarith [Real.pow_nonneg (k+1) hy],?_⟩
  intro e he0 hey; specialize hC2 e he0 hey
  rw [pow_succ'];
  calc
    _ ≥ (y - e) * (y^(k+1) - C * e) := by gcongr; linarith
    _ = y* (y^(k+1) - C * e) - e*y^(k+1) + C*(e*e) := by ring_nf
    _ ≥ y* (y^(k+1) - C * e) - e*y^(k+1) + (-C*e) := by gcongr 1; nlinarith
    _ = _ := by ring_nf;

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
y = x.root n ↔ y^n = x := by
  have hlub:= Real.root_LUB_rootset hx hn;
  rw [isLUB_def, upperBound_def] at hlub
  obtain ⟨h1, h2⟩ := hlub
  constructor <;> intro h
  · apply le_antisymm -- →
    · contrapose! h2;
      have hy : y > 0 := by   by_contra hy0; have hy0 : y = 0 := by linarith
                              rw [← pow_eq_zero _ n (by linarith)] at hy0;
                              rw [hy0] at h2; linarith
      rw [← h] at *
      choose C hC1 hC2 using Real.linear_lower_bound_of_pow y n (by linarith) (by linarith)
      let e := min ( (y^n - x) / C) y
      use y - e; have he0 : e > 0 := by aesop
      simp [he0]; rw [upperBound_def, Real.rootset]
      intro r hr; simp at hr;
      apply pow_ge_pow_converse _ _ n ?_ (by simp [e]) hn
      apply le_trans hr.2;
      apply le_trans ?_ (hC2 e he0.le (min_le_right _ _))
      have := min_le_left ((y ^ n - x) / C) y
      simp [e]
      calc
        _ = y^n - C * ((y^n - x) / C) := by field_simp
        _ ≤ _ := by gcongr
    · contrapose! h1; rw [← h] at *
      choose C hC1 hC2 using Real.linear_upper_bound_of_pow y n (by linarith) (by linarith)
      let e := min ( (x - y^n) / C) 1
      use y + e; have he0 : e > 0 := by aesop
      simp [rootset, he0]
      refine ⟨ by linarith, ?_⟩
      apply le_trans (hC2 e he0.le (min_le_right _ _))
      have he2 : e ≤ (x - y ^ n) / C := min_le_left _ _
      calc
        _ ≤ y^n + C * ((x - y^n) / C) := by gcongr
        _ = x := by field_simp
  subst x -- ←
  apply le_antisymm
  · apply h1; simp [Real.rootset, hy]
  · apply h2; simp [upperBound_def, Real.rootset]; intro r hr1 hr2;
    apply pow_ge_pow_converse _ _ n hr2 hy hn

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  have hlub:= Real.root_LUB_rootset hx hn; rw [isLUB_def, upperBound_def] at hlub
  obtain ⟨h1, h2⟩ := hlub -- 0 is in rootset, so the LUB is ≥ 0
  apply h1; simp [Real.rootset]; field_simp [hx]

lemma lt_iff_ne_given_le {G: Type*} [LinearOrder G] {a b : G} (h : a ≤ b) : a < b ↔ a ≠ b := by
  constructor <;> intro h'; aesop; apply lt_of_le_of_ne h h';

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have := Real.root_nonneg hx hn
  simp; rw [lt_iff_ne_given_le this, lt_iff_ne_given_le hx]
  nth_rw 2 [show (0:Real) = 0^n by field_simp];
  rw [not_iff_not]; apply eq_root_iff_pow_eq; all_goals linarith

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  rw [← Real.eq_root_iff_pow_eq]; any_goals apply root_nonneg;
  all_goals assumption;

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  symm; rw [Real.eq_root_iff_pow_eq]; apply pow_nonneg
  all_goals assumption;

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  rw [← not_iff_not]; simp
  nth_rw 1 [← pow_of_root hx hn, ← pow_of_root hy hn]
  constructor <;> intro h <;> [apply Real.pow_ge_pow_converse; apply Real.pow_ge_pow]
  (any_goals apply h); (any_goals apply root_nonneg); (all_goals linarith)


theorem one_le_pow₀'{G : Type*} [MonoidWithZero G] [Preorder G] {a : G} [ZeroLEOneClass G] [PosMulMono G] (ha : 1 ≤ a) {n : ℕ} :
1 ≤ a ^ n := by
  by_cases hn : n = 0
  · simp_all
  apply le_trans ha (le_self_pow₀ ha hn)

lemma pow_le_pow_right' {G : Type*} [MonoidWithZero G] [Preorder G]
[ZeroLEOneClass G] [PosMulMono G] {a : G} {m n : ℕ}
(ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := by
  set k := n - m; rw [show n = m + k by omega]
  rw [← mul_one (a^m), ← Section_4_3.pow_add']
  apply mul_le_mul_of_nonneg_left
  apply one_le_pow₀' ha
  apply pow_nonneg (by apply le_trans zero_le_one ha)


theorem one_lt_pow₀'{G : Type*} [MonoidWithZero G] [Preorder G] {a : G} [ZeroLEOneClass G] [PosMulStrictMono G] (ha : 1 < a) {n : ℕ} (hn : n ≠ 0) :
1 < a ^ n := by
  obtain ⟨k,rfl ⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction' k with k ih
  · simp [ha]
  simp at *; rw [pow_succ];
  apply lt_trans ih; nth_rw 1 [← mul_one (a ^ (k + 1))]
  apply mul_lt_mul_of_pos_left ha (lt_of_le_of_lt zero_le_one ih)


lemma pow_lt_pow_right' {G : Type*} [MonoidWithZero G] [Preorder G]
[PosMulStrictMono G] [ZeroLEOneClass G]  {a : G} {m n : ℕ}
(h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := by
  by_cases hm : m = 0
  · subst m; simp; apply one_lt_pow₀' h
    linarith
  set k := n - m; rw [show n = m + k by omega]
  rw [← mul_one (a^m), ← Section_4_3.pow_add']
  apply mul_lt_mul_of_pos_left
  apply one_lt_pow₀' h
  unfold k; exact Nat.sub_ne_zero_iff_lt.mpr hmn
  apply lt_of_le_of_lt (zero_le_one) (one_lt_pow₀' h hm)

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  apply pow_gt_pow_converse _ _ l ?_ (by apply root_nonneg; all_goals linarith)
    (by linarith)
  rw [pow_of_root (by linarith) hl]
  nth_rw 1 [← pow_of_root (n := k) (x := x) (by linarith) (by linarith)]
  apply pow_lt_pow_right' ?_ hkl
  apply pow_gt_pow_converse _ _ k ?_ (by apply root_nonneg; all_goals linarith)
    (by linarith)
  simp; rw [pow_of_root (by linarith) (by linarith)]
  exact hx


/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  symm; rw [eq_root_iff_pow_eq]; all_goals simp [hk]

theorem Real.root_gt_one {x : Real} (hx: x > 1) {n: ℕ} (hn: n ≥ 1) : x.root n > 1 := by
  rw [← root_of_one (k:= n), ← root_mono]; all_goals linarith

theorem Real.root_ge_one {x : Real} (hx: x ≥ 1) {n: ℕ} (hn: n ≥ 1) : x.root n ≥ 1 := by
  by_cases h : x = 1
  · subst x; rw [root_of_one (k:= n)]; exact hn
  · have h' : x > 1 := by order
    apply le_of_lt; apply Real.root_gt_one h' hn

theorem Real.root_of_zero {k: ℕ} (hk: k ≥ 1) : (0:Real).root k = 0 := by
  symm; rw [eq_root_iff_pow_eq]; all_goals simp [hk];
  linarith

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  symm; rw [eq_root_iff_pow_eq, mul_pow, pow_of_root, pow_of_root]
  any_goals assumption;
  positivity
  apply mul_nonneg; all_goals apply root_nonneg
  any_goals assumption

theorem Real.root_inv {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : (x⁻¹).root n = (x.root n)⁻¹ := by
  have := (Real.root_pos hx.le hn).mpr hx
  field_simp [this]
  rw [← root_mul]; field_simp [hx]
  apply root_of_one
  any_goals positivity
  any_goals exact hn

-- Moved this one down so I could take the inverse and use the other method
-- Because I don't wanna redo the other method slightly more complicated, boring
/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  have hkp := (Real.root_pos hx0.le hl).mpr hx0
  have hlp := (Real.root_pos (n:= k) hx0.le (by linarith)).mpr hx0
  simp; rw [← inv_lt_inv₀ hlp hkp, ← root_inv hx0 hl, ← root_inv (n:=k) hx0 (by linarith)]
  rw [← one_lt_inv₀ hx0] at hx
  apply Real.root_mono_of_gt_one (x := x⁻¹) hx hkl hl

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  have : x.root n ≥ 0 := by apply root_nonneg hx hn;
  rw [eq_root_iff_pow_eq]; rw [mul_comm, ← pow_mul, pow_of_root, pow_of_root]
  any_goals assumption;
  apply root_nonneg this; all_goals nlinarith

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  symm; rw [eq_root_iff_pow_eq]; all_goals linarith

/-
This is basically the same as pow_inj from last chapter
But now we have a funny way to prove it
-/
theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  rw [← eq_root_iff_pow_eq] at h
  rw [h]; apply root_of_pow; any_goals apply pow_nonneg
  all_goals linarith

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

lemma Real.pow_root_cancel {x : Real} {a: ℤ  } {b c: ℕ } (hb: b > 0) (hc: c > 0) (hx: x > 0) :
( x.root b ) ^ a = (x.root (b * c))^(a * c) := by
  rw [← root_root, mul_comm, ← zpow_mul, Section_4_3.pow_eq_zpow'' , pow_of_root]
  apply root_nonneg; any_goals linarith

lemma Real.pow_root_cancel' {x : Real} {a: ℤ  } {b c: ℕ } (hb: b > 0) (hc: c > 0) (hx: x > 0) :
( x.root b ) ^ a = (x.root (c * b))^(c * a) := by
  rw [mul_comm c b, mul_comm (c:ℤ) a]
  apply Real.pow_root_cancel hb hc hx

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  wlog ha: a > 0 generalizing a b a' b'
  · simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    · -- Negative exp can turn into positive by inverting both sides
      replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by -- Cast to ℤ, turn to neg
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by -- If a' = 0, then a = 0
      subst a; field_simp [hb'] at hq; symm; exact_mod_cast hq;
    simp_all -- This case is simple: both sides are 1
  have : a' > 0 := by
    have : a * b' > 0 := by positivity
    field_simp [hb'] at hq; norm_cast at hq; rw [hq] at this
    nlinarith
  field_simp at hq
  -- Modified using pow_root_cancel
  lift a to ℕ using by order
  lift a' to ℕ using by order
  rw [pow_root_cancel (c := a) ]
  norm_cast at hq; rw [mul_comm, hq, mul_comm]; nth_rw 2 [mul_comm]
  rw [← pow_root_cancel (c := a')]
  all_goals linarith

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  · have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  rw [show (1:ℚ) = (1:ℤ) by simp, Real.ratPow_def ]
  simp; all_goals linarith

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  rw [show (n:ℚ) = (n/(1:ℕ):ℚ) by simp, Real.ratPow_def, root_one ]
  all_goals tauto

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [Real.ratPow_def]
  apply zpow_pos; rw [root_pos]; any_goals linarith

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  rw [show ((a/b) + (c/d):ℚ) = ((a*d + b*c):ℤ)/(b*d:ℕ) by field_simp; ring]
  repeat rw [Real.ratPow_def]
  rw [pow_root_cancel (b := b) (c := d), pow_root_cancel' (b := d) (c := b)]
  rw [zpow_add]
  apply ne_of_gt; rw [← gt_iff_lt, root_pos]
  any_goals positivity
  suffices b*d > 0 by linarith
  positivity


theorem Real.root_pow_eq_pow_root {x:Real} {a:ℤ} {b:ℕ} (hb: b > 0) (hx : x ≥ 0):
  (x^a).root b = (x.root b)^a := by
  symm; rw [Real.eq_root_iff_pow_eq]
  rw [← Section_4_3.pow_eq_zpow'', zpow_mul, mul_comm, ← zpow_mul, Section_4_3.pow_eq_zpow'']
  rw [pow_of_root]
  any_goals apply zpow_nonneg
  any_goals apply root_nonneg
  any_goals linarith

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  rw [Real.ratPow_def, Real.ratPow_def]
  rw [root_pow_eq_pow_root, root_root, zpow_mul]
  rw [← Real.ratPow_def]; congr; field_simp
  any_goals apply root_nonneg
  any_goals linarith
  positivity
  rw [Real.ratPow_def]; apply zpow_pos; rw [root_pos]; any_goals linarith


/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [show - (a/b:ℚ) = (-a:ℤ)/b by field_simp, Real.ratPow_def, Real.ratPow_def]
  field_simp; all_goals assumption

theorem Real.ratPow_neg' {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = (1 / x)^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_neg, Real.ratPow_def, Real.ratPow_def]
  simp; rw [Real.root_inv]; simp
  any_goals linarith
  positivity

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  field_simp at h
  lift a to ℕ using by omega
  rw [Real.ratPow_def, Real.ratPow_def]
  constructor <;> intro hxy
  · apply pow_gt_pow; rw [← root_mono]; exact hxy
    any_goals apply root_nonneg;
    any_goals linarith
  · rw [root_mono (n := b)]; apply pow_gt_pow_converse _ _ a
    convert hxy
    apply root_nonneg; any_goals linarith
  any_goals assumption

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  have : b*d > 0 := by nlinarith
  nth_rw 1 [show (a/b:ℚ) = (a*d: ℤ )/(b*d:ℕ)  by field_simp; ring,
      show (c/d:ℚ) = (b*c: ℤ)/(b*d:ℕ) by field_simp; ring]
  rw [Real.ratPow_def, Real.ratPow_def]
  constructor <;> intro hxy
  · contrapose! hxy; rw [div_le_div_iff₀] at hxy
    rw [← ge_iff_le]; apply zpow_le_zpow_right₀ -- Similar to proven theorems
    apply Real.root_ge_one
    any_goals linarith
    norm_cast at hxy; linarith
    any_goals positivity
  · rw [gt_iff_lt, div_lt_div_iff₀] at hxy;
    rw [gt_iff_lt]; apply zpow_lt_zpow_right₀; apply Real.root_gt_one
    any_goals linarith
    norm_cast at hxy; linarith
    any_goals positivity
  any_goals positivity

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  nth_rw 1 [show q = -(-q) by ring, show r = -(-r) by ring]
  rw [ratPow_neg']; nth_rw 2 [ratPow_neg']; simp
  rw [← gt_iff_lt, Real.ratPow_mono_of_gt_one (x := x⁻¹)]
  simp; rw [gt_iff_lt,one_lt_inv₀ hx0]
  all_goals linarith

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [Real.ratPow_def, Real.ratPow_def, Real.ratPow_def]
  rw [← mul_zpow, root_mul]
  any_goals positivity
  linarith

-- I could nuke this with positivity but I won't
theorem Real.squared_nonneg (x:Real) : x^2 ≥ 0 := by
  by_cases h : x ≥ 0
  · apply pow_nonneg; exact h
  · have : -x > 0 := by linarith
    rw [show x^2 = (-x)^2 by ring]
    apply pow_nonneg; linarith

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
  rw [mul_comm, ← pow_mul]
  apply Real.squared_nonneg

/-
Exercise 5.6.4 If x is a real number, show that |x| = (x^2)^(1/2).
-/

theorem Real.abs_eq_sqrt_of_sq (x:Real) (hx : x ≠ 0) : |x| = (x^2)^(1/2:ℚ) := by
  wlog h : x > 0
  · have h0: -x > 0 := by
      apply lt_of_le_of_ne (by linarith) (by simp; apply hx)
    specialize this (-x) (by aesop) (by push_neg at h; linarith)
    rw [show ( |-x| = |x|) by simp, show ( (-x)^2 = x^2) by ring] at this
    exact this
  rw [show (1/2:ℚ) = (1/(2:ℕ)) by simp, ratPow_eq_root]
  rw [Real.root_of_pow]
  rw [_root_.abs_of_pos h]
  any_goals linarith
  positivity

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  by_cases hxy : x ≥ y
  · simp [hxy]; contrapose! hxy
    rw [← gt_iff_lt, Real.ratPow_mono];
    all_goals assumption
  · simp at hxy; simp [hxy.le]; apply le_of_lt;
    rw [← gt_iff_lt, ← Real.ratPow_mono];
    all_goals assumption



/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  by_cases hxy : x ≥ y
  · simp [hxy]; contrapose! hxy
    rw [← gt_iff_lt, Real.ratPow_mono];
    all_goals assumption
  · simp at hxy; simp [hxy.le]; apply le_of_lt;
    rw [← gt_iff_lt, ← Real.ratPow_mono];
    all_goals assumption

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.


theorem Real.max_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  max (x^q) (y^q) = (min x y)^q := by
  nth_rw 1 [show q = -(-q) by ring]; nth_rw 2 [show q = -(-q) by ring]
  rw [ratPow_neg']; nth_rw 2 [ratPow_neg']; simp
  rw [max_ratPow, ← Real.inv_min, ratPow_neg']; simp
  any_goals positivity
  any_goals linarith
  simp_all [isPos_iff]; simp_all [isPos_iff]

theorem Real.min_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  min (x^q) (y^q) = (max x y)^q := by
  nth_rw 1 [show q = -(-q) by ring]; nth_rw 2 [show q = -(-q) by ring]
  rw [ratPow_neg']; nth_rw 2 [ratPow_neg']; simp
  rw [min_ratPow, ← Real.inv_max, ratPow_neg']; simp
  any_goals positivity
  any_goals linarith
  simp_all [isPos_iff]; simp_all [isPos_iff]

end Chapter5
