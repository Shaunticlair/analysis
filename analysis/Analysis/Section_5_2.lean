import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  simp [Rat.closeSeq_def]; intro n hn; simp [hn]
  lift n to ℕ using hn
  by_cases h: Even n <;> rw [Rat.Close]
  · simp [h.neg_one_pow];
    rw [abs_of_neg] <;> norm_num;
  · observe h': Odd n
    simp [h'.neg_one_pow];
    rw [abs_of_nonneg] <;> norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
:= by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence)
:= by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 1; simp [Rat.Close] at h
  rw [abs_of_nonneg] at h; norm_num at h; norm_num

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl



/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔  ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  rw [Rat.eventuallyClose_def]
  constructor <;> intro h <;> choose N h using h
  · let N' := max N 0; use N'.toNat
    intro n hn
    specialize h n (by simp; omega) (by simp; omega)
    simp [show n ≥ N by omega] at h; exact h
  · use N; simp [Rat.CloseSeq];
    intro n hn; lift n to ℕ using (by linarith)
    simp [hn]; exact h n (by linarith)

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  intro h; specialize h 0 (by simp) (by simp); simp at h;
  rw [Rat.Close, abs_of_nonneg] at h <;> norm_num at *

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  use 1; simp [Rat.CloseSeq]; intro n hn; simp [hn, show 0 ≤ n by linarith]
  rw [Rat.Close, abs_of_nonneg]; norm_num; simp; ring_nf;
  rw [show -1 - n = -(1+n) by ring];
  calc
    _ ≤ (10:ℚ) ^ (-(2:ℤ)) * 2 := by gcongr; norm_num; linarith
    _ ≤ 1 / 10 := by norm_num
  field_simp; apply zpow_nonneg (by norm_num)

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  use 2; simp [Rat.CloseSeq]; intro n hn; simp [hn, show 0 ≤ n by linarith]
  rw [Rat.Close, abs_of_nonneg]; norm_num; simp; ring_nf;
  rw [show -1 - n = -(1+n) by ring];
  calc
    _ ≤ (10:ℚ) ^ (-(3:ℤ)) * 2 := by gcongr; norm_num; linarith
    _ ≤ 1 / 100 := by norm_num
  field_simp; apply zpow_nonneg (by norm_num)

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor <;> intro h e he <;> specialize h e he
  <;> rw [Rat.eventuallyClose_iff] at * <;> exact h

lemma ten_pow_geq (N : ℕ ) : 10^N ≥ N := by
  have h1 := pow_le_pow_left₀ (a:= 2) (b:= 10) (by norm_num) (by norm_num)
  refine le_trans ?_ (h1 N)
  exact Section_4_3.two_pow_geq N

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans ?_ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

lemma Close_symm {ε:ℚ} {a b: ℚ} (hab: ε.Close a b) : ε.Close b a := by
  rw [Rat.Close] at *; rwa [abs_sub_comm] at hab

lemma Sequence.closeSeq_symm {ε:ℚ} {a b: Chapter5.Sequence} (hab: ε.CloseSeq a b) :
    ε.CloseSeq b a := by
  rw [Rat.closeSeq_def] at *;
  intro hn hb ha; specialize hab _ ha hb
  apply Close_symm hab

lemma Sequence.eventuallyClose_symm {ε:ℚ} {a b: Chapter5.Sequence}
    (hab: ε.EventuallyClose a b) : ε.EventuallyClose b a := by
  rw [Rat.eventuallyClose_def] at *; choose N hN using hab; use N;
  apply Sequence.closeSeq_symm hN

lemma Sequence.equiv_symm {a b: ℕ → ℚ} (hab: Equiv a b) : Equiv b a := by
  rw [Sequence.equiv_def] at *;
  peel hab with ε hε hab --intro ε hε; specialize hab ε hε
  apply Sequence.eventuallyClose_symm hab

theorem Sequence.isCauchy_of_equiv' {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy → (b:Sequence).IsCauchy := by
  intro ha; intro e he;
  specialize ha (e/3) (by linarith); specialize hab (e/3) (by linarith);
  choose N hN ha using ha; choose M hab using hab; simp at hN

  refine ⟨max N M, by simp_all, ?_⟩
  intro n hn m hm; simp at hn hm

  specialize ha n (by simp [hn]) m (by simp [hm])
  have hab1 := hab n (by simp [hn]) (by simp [hn])
  have hab2 := hab m (by simp [hm]) (by simp [hm])
  simp_all;
  apply Close_symm at hab1
  have h1 := Section_4_3.close_trans hab1 ha
  have h2 := Section_4_3.close_trans h1 hab2
  convert h2; linarith

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  constructor <;> apply Sequence.isCauchy_of_equiv'
  · apply hab
  · apply (Sequence.equiv_symm hab)

theorem Sequence.isBounded_of_eventuallyClose' {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded → (b:Sequence).IsBounded := by
  intro ha;
  rw [Sequence.isBounded_def.coe] at *; rw [Rat.eventuallyClose_iff] at hab
  choose A hA ha using ha; choose N hab using hab;
  -- Finite region of b bounded by B
  let fin : Fin N → ℚ := fun m ↦ b m
  obtain ⟨ B, hBpos, hB ⟩ := IsBounded.finite fin
  have h1 : Chapter5.BoundedBy fin ( B + (A + |ε| )) := fun m ↦ (hB m).trans (by simp; positivity)
  -- ε-close region is bounded by A + |ε|
  have h2' (n : ℕ ) (hn : n ≥ N) : |b n| ≤ A + |ε| := by
    rw [show b n = a n + (b n - a n) by ring]
    have := abs_add (a n) (b n - a n); specialize ha n; specialize hab n hn
    rw [abs_sub_comm] at hab; have:= (le_abs_self ε);
    linarith

  have h2 (n : ℕ ) (hn : n ≥ N) : |b n| ≤ B + (A + |ε|) := by linarith [h2' n hn]

  refine ⟨ B + (A + |ε| )  , by positivity, ?_ ⟩
  intro n;
  by_cases hn : n < N
  · specialize h1 ⟨ n, hn ⟩; apply h1;
  · push_neg at hn; exact h2 n hn

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  constructor <;> apply Sequence.isBounded_of_eventuallyClose'
  · apply hab
  · apply Sequence.eventuallyClose_symm hab

end Chapter5
