import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hx0 : x = 0
  · left; exact hx0
  · right; choose a hac hab hax using Real.boundedAwayZero_of_nonzero hx0
    choose c hc hca using hab
    choose N hN hNc using hac (c/2) (half_pos hc); simp at hN
    lift N to ℕ using (by linarith)
    specialize hca N
    -- Create truncated sequence: valid equivalent for a, doesn't cross through zero
    let b := Real.truncated_seq N (a N) a
    have hbc := Real.truncated_seq_equiv N (a N) a
    have hbcauchy := (Sequence.isCauchy_of_equiv hbc).mp hac
    -- b is either positive or negative: cases nearly identical
    by_cases hcaN : a N > 0 <;>
    simp at hcaN <;> [left; right] <;>
    [apply abs_of_pos at hcaN; apply abs_of_nonpos at hcaN] <;>
    simp [hcaN] at hca <;>
    refine ⟨b, ?_, hbcauchy, by rw [hax, (LIM_eq_LIM hac hbcauchy ).mpr hbc]⟩<;>
    (use c/2, half_pos hc; intro n) <;>
    (by_cases hn: n < N <;> simp [b, Real.truncated_seq, hn]; linarith) <;>
    specialize hNc n (by simp; linarith) N (by simp) <;>
    push_neg at hn <;> simp [hn, Rat.Close] at hNc
    · by_cases hnan : a n - a N ≥ 0
      · rw [abs_of_nonneg hnan] at hNc; linarith -- If a n ≥ a N, then c-bound holds
      -- Else, a n + c/2 ≥ a N ≥ c: a n is stuck within c/2 of a N
      · push_neg at hnan; simp [abs_of_neg hnan] at hNc; linarith
    · by_cases hnan : a n - a N ≤ 0
      · rw [abs_of_nonpos hnan] at hNc; linarith -- Below a N: c-bound holds
      · push_neg at hnan; simp [abs_of_pos hnan] at hNc; linarith

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  intro ⟨h1,h2⟩; contrapose! h1
  choose a hab hac hax using h2
  rw [hax]
  apply Real.lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayPos hab) hac

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  intro ⟨h1,h2⟩; contrapose! h1
  choose a hab hac hax using h2
  rw [hax]
  apply Real.lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayNeg hab) hac

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  intro ⟨h1,h2⟩;
  choose a hap hac hax using h1 -- a and b are fenced on opposite sides of 0
  choose z hz haz using hap
  choose b han hbc hbx using h2
  choose w hw hbw using han

  rw [hax, LIM_eq_LIM hac hbc, Sequence.equiv_iff] at hbx;
  choose N hN using hbx ((z+w)/2) (by linarith) -- an and bn should be eventually close
  specialize hN N (by linarith); specialize haz N; specialize hbw N;
  rw [abs_of_nonneg (by linarith)] at hN
  contrapose! hN; linarith -- But they can't get closer than the fences allow

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor <;> intro h <;> choose a ha hac hax using h
  <;> refine ⟨-a, by peel 3 ha with c hc n hcn; simp; linarith,
              Sequence.IsCauchy.neg _ hac, ?_⟩
  <;> simp [← Real.neg_LIM _ hac, ← hax]

theorem Real.pos_iff_neg_of_pos (x:Real) : x.IsPos ↔ (-x).IsNeg := by
  constructor <;> intro h <;> choose a ha hac hax using h
  <;> refine ⟨-a, by peel 3 ha with c hc n hcn; simp; linarith,
              Sequence.IsCauchy.neg _ hac, ?_⟩
  <;> simp [← Real.neg_LIM _ hac, ← hax]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  choose a hap hac hax using hx; choose A hA0 hA using hap
  choose b hbp hbc hby using hy; choose B hB0 hB using hbp
  refine ⟨a + b, ?_, (hac.add hbc), by rw [hax, hby, Real.LIM_add hac hbc]⟩
  refine ⟨A+B, by linarith, ?_⟩
  intro n; simp; linarith [hA n, hB n]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  choose a hap hac hax using hx; choose A hA0 hA using hap
  choose b hbp hbc hby using hy; choose B hB0 hB using hbp
  refine ⟨a * b, ?_, (hac.mul hbc), by rw [hax, hby, Real.LIM_mul hac hbc]⟩
  refine ⟨A*B, by nlinarith, ?_⟩
  intro n; simp; nlinarith [hA n, hB n]

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor <;> intro h
  · contrapose! h; rw [le_iff_lt_or_eq] at h
    rcases h with h | h
    · rw [pos_iff_neg_of_pos]; intro hneg; apply not_pos_neg
      refine ⟨?_, hneg⟩;  use (fun _ ↦ -q);
      refine ⟨by use (-q); simp [h], ⟨Sequence.IsCauchy.const _, ?_⟩⟩
      rw [ratCast_def]; rw [neg_LIM];
      congr; apply Sequence.IsCauchy.const
    subst h;
    intro h; apply not_zero_pos; refine ⟨?_, h⟩; simp
  · refine ⟨(fun _ ↦ q),?_, Sequence.IsCauchy.const _, ratCast_def q⟩
    use q; simp [h]

theorem Real.pos_of_coe' (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor <;> intro h
  · contrapose! h; rw [le_iff_lt_or_eq] at h
    rcases h with h | h
    · intro hpos; apply not_pos_neg
      refine ⟨hpos, ?_⟩;  use (fun _ ↦ q);
      refine ⟨by use (-q); simp [h], ⟨Sequence.IsCauchy.const _, ?_⟩⟩
      rw [ratCast_def]
    subst h;
    intro h; apply not_zero_pos; refine ⟨?_, h⟩; simp
  · refine ⟨(fun _ ↦ q),?_, Sequence.IsCauchy.const _, ratCast_def q⟩
    use q; simp [h]


#check Real.neg_ratCast
theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  simp; rw [Real.neg_ratCast, pos_of_coe]; simp

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  simp [lt_iff]

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  simp [le_iff, show y = x ↔ x = y by aesop]

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  simp only [lt_iff, ratCast_sub, Real.neg_of_coe (q - q'), sub_neg]

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by simp [gt_iff]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by simp [lt_iff]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  convert Real.trichotomous (x - y) using 0;
  rw [← gt_iff, ← lt_iff, sub_eq_zero]; tauto

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]; apply not_pos_neg

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
rw [gt_iff, ← sub_eq_zero, And.comm]; apply not_zero_pos (x-y)

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
rw [lt_iff, ← sub_eq_zero, And.comm]; apply not_zero_neg (x-y)

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by rfl

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [antisymm, gt_iff] at *; convert pos_add hxy hyz using 1; ring

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [lt_iff] at *; simp_all

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rw [le_iff] at *;
  rcases hxy with (hxy | rfl)
  · left; convert mul_lt_mul_right hxy hz using 1 <;> ring
  · simp

theorem Real.mul_le_mul_right {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : x * z ≤ y * z := by
  rw [mul_comm x z, mul_comm y z]; apply Real.mul_le_mul_left hxy hz

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  rw [neg_iff_pos_of_neg] at *; convert pos_mul hx hy using 1; ring

theorem Real.mul_lt_mul_right_mt {x y z:Real} (hxy: x * z < y * z) (hz: z.IsPos) : x < y := by
  rw [antisymm, gt_iff, show y*z-x*z=(y-x)*z by ring] at *;
  rcases Real.trichotomous (y - x) with h' | h' | h'
  · simp [h'] at hxy; exfalso;
    apply nonzero_of_pos hxy rfl;
  · exact h'
  · exfalso; apply not_pos_neg; refine ⟨hxy, ?_⟩;
    convert mul_pos_neg hz h' using 1; ring

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by intro a; rw [le_iff]; tauto
  le_trans := by
    intro a b c hab hbc; rw [le_iff] at *
    rcases hab with (hab | rfl) <;> rcases hbc with (hbc | rfl) <;> try tauto
    · left; exact lt_trans hab hbc
  lt_iff_le_not_ge := by
    intro a b; simp [le_iff]; push_neg
    constructor <;> intro h
    · refine ⟨by left; exact h, ⟨?_, ?_⟩⟩
      · have := not_gt_and_lt a b; tauto
      · simp [Eq.comm]; have := not_lt_and_eq a b; tauto
    · have := trichotomous' a b; tauto
  le_antisymm := by
    intro a b hab hba; rw [le_iff] at *;
    rcases hab with (hab | rfl) <;> rcases hba with (hba | hba); any_goals rfl
    · exfalso; apply not_gt_and_lt a b ⟨hba, hab⟩
    · symm; exact hba
  le_total := by
    intro a b; repeat rw [le_iff]
    rcases Real.trichotomous' a b with (hab | hab | hab) <;> tauto
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/
@[simp]
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  rcases Real.trichotomous x with h | h | h <;> simp [h, _root_.abs]
  · have hp := h; rw [isPos_iff] at hp
    have hn := h; rw [pos_iff_neg_of_pos] at hn; rw [isNeg_iff] at hn
    order
  · have hp := h; rw [isNeg_iff] at hp
    have hn := h; rw [neg_iff_pos_of_neg] at hn; rw [isPos_iff] at hn
    order

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  simpa [hinv_non, hnonneg] using (trichotomous x⁻¹)

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  convert (Real.pos_mul hx (Real.inv_of_pos hy)) using 1

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

theorem Real.mul_lt_mul_left {x y z:Real} (hxy: x < y) (hz: z.IsPos) : z * x < z * y := by
  rw [antisymm, gt_iff] at *; convert pos_mul hxy hz using 1; ring

theorem Real.self_inv_mul {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm]; apply self_mul_inv hx

-- My preferred way to prove inv_of_gt
theorem Real.inv_of_gt' {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  have hxinv : x⁻¹.IsPos := Real.inv_of_pos hx
  have hyinv : y⁻¹.IsPos := Real.inv_of_pos hy
  have : x * x⁻¹ > y * x⁻¹ :=  mul_lt_mul_right hxy hxinv
  have : y⁻¹ * (x * x⁻¹) > y⁻¹ * (y * x⁻¹) := mul_lt_mul_left this hyinv
  simpa [self_mul_inv hxnon, ← mul_assoc, self_inv_mul hynon] using this

theorem Real.add_le_add_right' (a b :Real) (hab: a ≤ b) (c : Real): a + c ≤ b + c := by
  rw [le_iff] at *
  rcases hab with (hab | rfl)
  · left; exact Real.add_lt_add_right _ hab
  · right; rfl

theorem Real.mul_lt_mul_of_pos_right' (a b c :Real) (hab: a < b) (hc: 0 < c) : a * c < b * c := by
  simp [← isPos_iff] at hc
  apply mul_lt_mul_right hab hc

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b hab c; rw [add_comm c a, add_comm c b]
    apply Real.add_le_add_right'; exact hab
  add_le_add_right := Real.add_le_add_right'
  mul_lt_mul_of_pos_left := by
    intro a b c hab hc; rw [mul_comm c a, mul_comm c b]
    apply mul_lt_mul_of_pos_right' _ _ _ hab hc
  mul_lt_mul_of_pos_right := Real.mul_lt_mul_of_pos_right'
  le_of_add_le_add_left := by
    intro a b c habc; rw [add_comm a b, add_comm a c] at habc
    rw [le_iff] at *; rcases habc with (habc | habc)
    · left; rw [lt_iff] at *; simp at habc
      rw [pos_iff_neg_of_pos] at habc
      simpa using habc
    · right; simpa using habc
  zero_le_one := by
    rw [le_iff]; left; simp [lt_iff];
    rw [Real.OfNat_eq_ratCast, pos_of_coe]; norm_num

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use ((fun (n:ℕ) ↦ (1:ℚ) ) + (fun (n:ℕ) ↦ 1/((n:ℚ) + 1)))
  use ((fun (n:ℕ) ↦ (1:ℚ) ) - (fun (n:ℕ) ↦ 1/((n:ℚ) + 1)))
  have hch:= Sequence.IsCauchy.harmonic'
  have hx1 := Sequence.IsCauchy.const 1
  constructor; convert Sequence.IsCauchy.add hx1 hch
  constructor; convert Sequence.IsCauchy.sub hx1 hch
  constructor; intro n; simp; have : ((n:ℚ) + 1)⁻¹ > 0 := by positivity
  linarith;
  push_neg; rw [le_iff]; right
  rw [← LIM_add hx1 hch, ← LIM_sub hx1 hch, Real.LIM.harmonic]; simp

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  · convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

theorem Real.exists_rat_le {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x):=  (exists_rat_le_and_nat_gt hx).1

theorem Real.exists_rat_lt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) < x) := by
  choose q hq1 hq2 using exists_rat_le hx
  use q/2; simp_all
  observe : 0 < (q:Real)
  linarith

theorem Real.exists_nat_gt (x:Real) :
    ∃ N:ℕ, x < (N:Real) := by
  obtain rfl | hx | hx := trichotomous x
  · use 1; simp
  · choose N _ using (exists_rat_le_and_nat_gt hx).2
    use N
  · rw [isNeg_iff] at hx
    use 0; simp [hx]

theorem Real.exists_rat_le_strong (x:Real):
  ∃ q:ℚ, (q:Real) ≤ x := by
  obtain rfl | hx | hx := trichotomous x
  · use -1; simp
  · choose q _ _ using exists_rat_le hx
    use q
  · have hx' := (neg_iff_pos_of_neg _).1 hx
    choose N _ using exists_nat_gt (-x)
    use -N; simp; linarith

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  · use 1; simpa [isPos_iff] using hε
  · choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  by_contra h
  conv at h => arg 1; arg 1; intro q; rw [and_comm]
  push_neg at h
  choose q hq using exists_rat_le_strong x
  observe hxy' : 0 < y - x
  choose r hr1 hr2 using exists_rat_lt ((isPos_iff  _).2 hxy')

  -- We're restricted from going between x and y. So, if q ≤ x, and we add some r
  -- small enough to not exceed y, then we still need to be q + r ≤ x
  -- We can repeat this process to get q + n*r ≤ x
  have hcontra (n : ℕ ): q + n * r ≤ x := by
    induction' n with n ih
    · simp_all
    · have : (((q + n * r + r):ℚ):Real) < y := by push_cast; linarith
      specialize h _ this;
      convert h; simp; ring

  -- This is absurd: we can always pick large enough n to exceed x, and cross the gap
  contrapose! hcontra
  choose n hn1 hn2 using le_mul ((isPos_iff r).2 (by norm_cast)) (x-q)
  use n; linarith


/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
apply existsUnique_of_exists_of_unique
· by_cases h0: x = 0
  · subst h0; use 0; simp
  wlog hpos : x > 0
  · have hlt: x < 0 := by push_neg at hpos; apply lt_of_le_of_ne hpos h0
    specialize this (-x) (by simp [h0]) (by linarith)
    choose n hn1 hn2 using this
    by_cases hxn : x = -(n:Real)
    · use -n; simp; refine ⟨by linarith, by linarith⟩
    · use -(n+1); simp;
      refine ⟨by linarith, ?_⟩
      apply lt_of_le_of_ne; linarith; exact hxn
  by_contra! h;
  have hcontra (n : ℕ ): n ≤ x := by
    induction' n with n ih
    · simp_all; linarith
    · specialize h n
      specialize h (by simp [ih])
      norm_cast at h
  choose N hN using exists_nat_gt x
  specialize hcontra N; linarith

· intro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
  by_cases heq : y = z
  · tauto
  · wlog hyz : y < z
    · specialize this x z y hz1 hz2 hy1 hy2 (by apply Ne.symm; apply heq)
      specialize this (by simp_all; apply lt_of_le_of_ne hyz (Ne.symm heq))
      exact Eq.symm this
    have : y + 1 ≤ z:= by linarith -- If y < z, then y+1 ≤ z
    have : (y : Real) + 1 ≤ (z : Real) := by norm_cast
    linarith -- But then, x < y+1 ≤ z


/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  choose N hN using exists_nat_gt (1/x)
  rw [isPos_iff] at hx;
  observe hpos : 0 < 1/x; observe hNpos : (N:Real) > 0
  use N; refine ⟨by norm_cast at *, ?_⟩
  simp_all; exact inv_lt_of_inv_lt₀ hx hN

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rcases Real.trichotomous (x-y) with ( hxy | hxy | hxy )
  · simp [hxy]
    constructor <;> intro h
    · refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_pos _ hxy]
    constructor <;> intro h
    · replace hxy := (isPos_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_neg _ hxy]
    constructor <;> intro h
    · replace hxy := (isNeg_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  rcases Real.trichotomous (x-y) with ( hxy | hxy | hxy )
  · simp [hxy]
    constructor <;> intro h
    · refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_pos _ hxy]
    constructor <;> intro h
    · replace hxy := (isPos_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith
  · simp [ abs_of_neg _ hxy]
    constructor <;> intro h
    · replace hxy := (isNeg_iff _ ).1 hxy
      refine ⟨by linarith, by linarith⟩
    · linarith

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor <;> intro h
  · by_contra! hcontra; specialize h ((x-y)/2) (by linarith)
    linarith
  · intro e he; linarith

theorem Real.ne_zero_abs_pos (x:Real) (h : x ≠ 0): |x| > 0 := by
  rcases Real.trichotomous x with ( rfl | hpos | hneg )
  · contradiction
  · simp [abs_of_pos _ hpos]; rw [isPos_iff] at hpos; linarith
  · simp [abs_of_neg _ hneg]; rw [isNeg_iff] at hneg; linarith

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor <;> intro h
  · contrapose! h;
    observe : x - y ≠ 0
    apply ne_zero_abs_pos at this
    use |x - y| / 2; simp_all
  · simp [h]; tauto

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
  LIM a ≤ x := by
    by_contra! hlim
    choose q hq1 hq2 using Real.rat_between hlim -- x < q < A
    contrapose! hq2; rw [ratCast_def q] -- A can't come after q:
    apply LIM_mono hcauchy (Sequence.IsCauchy.const q) -- a n ≤ x < q → a n ≤ q → A ≤ q
    intro n; specialize h n;
    suffices (a n : Real) ≤ (q : Real) by norm_cast at * -- Type management
    linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
  suffices LIM (-a) ≤ -x by rw [← neg_LIM _ hcauchy] at this; simpa using this
  apply Real.LIM_of_le (Sequence.IsCauchy.neg _ hcauchy) (by simpa)

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  simp [max_eq, min_eq]; split_ifs <;> simp

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  simp [max_eq, min_eq]; split_ifs <;> simp

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  simp [max_eq]; split_ifs <;> linarith

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  rw [max_eq]; split_ifs <;> rfl

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  by_cases h : y ≤ x <;> simp [max_eq] <;> simp [h]

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  by_cases h : y ≤ x <;> simp [max_eq];
  · simp [Real.mul_le_mul_right h hz, h]
  · simp only [h]; push_neg at h;
    simp [not_le_of_gt (Real.mul_lt_mul_right h hz)]

/- Additional exercise: What happens if z is negative? -/
theorem Real.max_mul_neg (x y :Real) {z:Real} (hz: z.IsNeg) : max (x * z) (y * z) = min x y * z := by
  rw [neg_iff_pos_of_neg] at hz
  rw [neg_min, show -max (-x) (-y) * z = max (-x) (-y) * -z by ring]
  simp [← max_mul (-x) (-y) hz]


/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  simp [min_eq]; split_ifs <;> linarith

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [min_eq]; split_ifs <;> rfl

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  by_cases h : x ≤ y <;> simp [min_eq] <;> simp [h]

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  simp [neg_min, ← max_mul _ _ hz]

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  by_cases h : y ≤ x <;> simp [max_eq, min_eq];
  · rw [isPos_iff] at *; simp [h, (inv_le_inv₀ hx hy).mpr h]
  · simp only [h]; push_neg at h;
    simp [not_le_of_gt (Real.inv_of_gt hy hx h)]

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  by_cases h : x ≤ y <;> simp [min_eq, max_eq];
  · rw [isPos_iff] at *; simp [h, (inv_le_inv₀ hy hx).mpr h]
  · simp only [h]; push_neg at h;
    simp [not_le_of_gt (Real.inv_of_gt hx hy h)]

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by intro x y hxy; simp [hxy]

end Chapter5
