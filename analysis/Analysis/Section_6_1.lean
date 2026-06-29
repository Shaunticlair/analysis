import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $ε$-closeness, $ε$-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from ℤ to ℝ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from ℕ to ℝ can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  a.from n₁ starts `a:Sequence` from `n₁`.  It is intended for use when `n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence `a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

lemma Sequence.from_start (a:Sequence) {N :ℤ} (hn: N ≥ a.m): (a.from N).m = N := by simp_all

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed s, the function ε ↦ ε.Steady s is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed s, the function ε ↦ ε.EventuallySteady s is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-Unpacked cauchy def-/
lemma Sequence.isCauchy_def' (a:Sequence):
  a.IsCauchy ↔ ∀ ε > 0, ∃ N ≥ a.m, ∀ n ≥ N, ∀ m ≥ N, dist (a n) (a m) ≤ ε := by
  peel with e he N hN n; rw [from_start]; peel with hn m hm;
  rw [from_eval, from_eval] <;> linarith; linarith

/-- This is almost the same as Chapter5.Sequence.IsCauchy.coe -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

#check Chapter5.Real.ratCast_sub

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
  peel with n hn m hm; simp [Rat.Close, dist];
  rw [← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_le]

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
  peel with q hq; rw [is_steady_of_rat]; grind


/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  · intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε -- Choose a smaller ε' that is rational
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
    unfold TendsTo Real.EventuallyClose Real.CloseSeq Real.Close;
    peel with e he;
    constructor <;> rintro ⟨N, h⟩ <;> use max N a.m
    · intro n hn; have ⟨h1, h2⟩ := h; specialize h2 n (by grind)
      rw [Real.dist_eq] at h2; grind
    refine ⟨by simp, ?_⟩; intro n hn
    rw [Real.dist_eq]; grind

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)






/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h; specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  rw [Real.eventuallyClose_def, seq_6_1_6]; use 1; simp [Real.CloseSeq]
  intro n hn; simp [hn, (by linarith: 0 ≤ n)]
  rw [show (1e-2:ℝ) = 10^(-2:ℤ) by norm_num]
  gcongr <;> grind

#check exists_nat_gt


/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  intro e he; choose N hN using exists_nat_gt (1/e)
  use N+1; simp [seq_6_1_6, Real.CloseSeq]; refine ⟨by linarith, ?_⟩
  intro n hn0 hnp; simp [hn0, hnp];
  replace hnp : (N:ℝ) + 1 ≤ n := by exact_mod_cast hnp
  lift n to ℕ using (by linarith)
  have : (n+1:ℝ) ≤ (10:ℝ)^(n+1:ℤ) := by exact_mod_cast Chapter5.ten_pow_geq (n+1)
  rw [show -(n:ℤ)-1 = -(n+1) by ring, ← inv_inv (a := e)];
  nth_rw 2 [← one_div]; rw [zpow_neg]; gcongr;
  simp at hnp; linarith




/-
e : ℝ
N : ℕ
n : ℕ
he : e > 0
hN : 1 / e < (N : ℝ)
this : (10:ℕ) ^ (n + 1) ≥ n + 1
hnp : (N:ℤ) + 1 ≤ (n:ℤ)
⊢ 1 / e ≤ 10 ^ ((n:ℤ) + 1)
-/


/-
e : ℝ
N : ℕ
n : ℕ
he : e > 0
hN : 1 / e < (N : ℝ)
this : (10:ℕ) ^ ((n:ℤ) + 1) ≥ n + 1
hnp : (N:ℤ) + 1 ≤ (n:ℤ)
⊢ 1 / e ≤ 10 ^ ((n:ℤ) + 1)
-/

/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

theorem Sequence.tendsTo_unique' (a:Sequence) {L L':ℝ} (hL: a.TendsTo L) (hL': a.TendsTo L'):
L = L' := by have hLand := And.intro hL hL'; contrapose! hLand; apply tendsTo_unique at hLand; tauto

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of 0 if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h




/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  choose L hL using h; intro e he; specialize hL (e/3) (by positivity); choose N hN hL using hL
  refine ⟨N, hN, ?_⟩; intro n hn m hm; have hn:= hL n hn; have hm:= hL m hm
  rw [Real.close_def] at *; apply le_trans (dist_triangle _ L _)
  rw [dist_comm] at hm; linarith


/-- Example 6.1.13 -/
example : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  rw [Real.eventuallySteady_def]; push_neg; --rw [Real.steady_def]; push_neg
  intro N hN; rw [Real.steady_def]; push_neg
  refine ⟨N, by simp [hN], N+1, by simp [hN], ?_⟩
  rw [Real.close_def]; push_neg;
  simp at hN; lift N to ℕ using hN; simp [show 0 ≤ (N:ℤ)+1 by linarith]
  rw [pow_succ]; simp [dist];
  by_cases hN : Even N
  · simp [hN]; norm_num
  simp at hN; simp [hN]; norm_num

/-- Example 6.1.13 -/
lemma ex6_1_13 : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  rw [Sequence.isCauchy_def]; push_neg; use 0.5; refine ⟨by norm_num, ?_⟩
  rw [Real.eventuallySteady_def]; push_neg; intro N hN; rw [Real.steady_def]; push_neg
  use N; simp at hN; simp [hN, dist]; use N+1; simp [show 0 ≤ (N:ℤ)+1 by linarith]
  lift N to ℕ using hN
  by_cases h : Even N
  · simp [h]; norm_num
  simp at h; simp [h]; norm_num

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  intro h; apply ex6_1_13; exact Sequence.IsCauchy.convergent h

/-
Exercise 6.1.6 Prove Proposition 6.1.15, using the following outline. Let (an)∞
n=1 be a Cauchy
sequence of rationals, and write L := LIMn→∞ an. We have to show that (an)∞
n=1 converges to L.
Let ε > 0. Assume for sake of contradiction that sequence an is not eventually ε-close to L. Use this,
and the fact that (an)∞
n=1 is Cauchy, to show that there is an N ≥ m such that either an > L + ε/2
for all n ≥ N, or an < L − ε/2 for all n ≥ N. Then use Exercise 5.4.8.
-/

#check Chapter5.Real.LIM_of_le

/-
This involves wrestling with ℝ machinery and I don't wanna do that right now.
-/

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by
  rw [Sequence.tendsTo_iff]; intro e he
  have ha := h ; rw [Chapter5.Sequence.IsCauchy.coe] at h
  sorry

/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

lemma Sequence.isBounded_finite' {a : Sequence} (k : ℕ) : ∃ M≥0, ∀ i < a.m + k, |a i| ≤ M := by
  induction' k with k ih
  · use 0; simp; intro i hi; rw [a.vanish i hi];
  choose M hM using ih; use max M (|a (a.m + k)|); simp [hM.1]
  intro i hi; simp [← add_assoc] at hi;
  rw [Int.lt_iff_add_one_le] at hi; simp at hi
  rcases Int.lt_or_eq_of_le hi with h | rfl
  · simp [hM.2 i h]
  simp

lemma Sequence.isBounded_finite (a : Sequence) (n : ℤ) : ∃ M ≥ 0, ∀ i < n, |a i| ≤ M := by
  by_cases h : n < a.m
  · use 0; simp; intro i hi; have := hi.trans h
    rw [a.vanish i this];
  convert isBounded_finite' ((n - a.m).toNat); simp_all

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  -- Split sequence into finite region and 1-steady region
  choose N hN h using h 1 (by norm_num)
  choose B hB0 hB using isBounded_finite a N
  use B + |a N| + 1; refine ⟨by positivity, ?_⟩
  intro i
  by_cases hi : i < N
  · specialize hB i hi; linarith [abs_nonneg (a.seq N)]
  simp at hi
  specialize h i (by simp; constructor <;> linarith) N (by simp [hN])
  rw [Real.close_def, Real.dist_eq, from_eval _ hi, from_eval _ (by rfl)] at h;
  rw [show a.seq i = a.seq N + (a.seq i - a.seq N) by ring]; apply le_trans (abs_add _ _ )
  linarith

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  apply bounded_of_cauchy; apply Sequence.IsCauchy.convergent h

/-- Example 6.1.18 -/
lemma ex_6_1_18 : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]; push_neg; intro M hM; choose n hn using (exists_nat_gt M)
  rw [Sequence.boundedBy_def]; push_neg; use n
  simp; norm_cast; simp; linarith

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  intro h; apply ex_6_1_18; apply Sequence.bounded_of_convergent h

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  rw [tendsTo_iff] at *;
  intro e he; specialize ha (e/2) (by positivity); specialize hb (e/2) (by positivity);
  choose A ha using ha; choose B hb using hb; use max A B; intro n hn
  specialize ha n (by grind); specialize hb n (by grind)
  simp; have := abs_add (a.seq n - L) (b.seq n - M)
  replace := this.trans (add_le_add ha hb)
  convert this using 1 <;> ring_nf


theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  choose L ha using ha; choose M hb using hb
  rw [← Sequence.lim_eq]; convert tendsTo_add ha hb
  <;> rw [lim_eq] at ha hb <;> simp_all

instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-
Duplicated from 4.3
-/
theorem Real.close_symm (ε x y:ℝ) : ε.Close x y ↔ ε.Close y x := by
  rw [Real.close_def, Real.close_def]; rw [dist_comm]

theorem Real.close_mul_mul' {ε δ x y z w:ℝ} (hxy: |x - y| ≤ ε) (hzw: |z - w| ≤ δ) :
    |x * z - y * w| ≤ ε * |z| + δ * |y| := by
    have h:= abs_add (x*z - y*z) (y*z - y*w);
    have h3: x*z - y*z = (x - y) * z := by ring;
    nth_rw 2 [h3] at h; rw [abs_mul] at h
    have h4: y*z - y*w = y * (z - w) := by ring
    nth_rw 2 [h4] at h; rw [abs_mul] at h; nth_rw 6 [mul_comm] at h
    calc
      _ = |x * z - y * z + (y * z - y * w)| := by ring_nf
      _ ≤ |x - y| * |z| + |z - w| * |y|:= h
    gcongr

/-- Theorem 6.1.19(b) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
  choose D hD0 hD using bounded_of_convergent (⟨M, hb⟩)
  rw [tendsTo_iff] at *;
  intro e he; specialize ha (e/(2*(|D|+1))) (by positivity);
  specialize hb (e/(2*(|L|+1))) (by positivity);
  choose A ha using ha; choose B hb using hb; use max A B; intro n hn
  specialize ha n (by grind); specialize hb n (by grind)
  simp;
  apply le_trans ( Real.close_mul_mul' ha hb )
  rw [boundedBy_def] at hD; specialize hD n; replace hD := hD.trans (le_abs_self D)
  nth_rw 3 [show e = e/2 + e/2 by ring]; gcongr
  · calc
      _ = e/2 * (|b.seq n|/(|D| + 1)) := by field_simp;
      _ ≤ e/2 * (|D|/(|D| + 1)) := by gcongr
      _ ≤ e/2 * 1 := by gcongr; exact div_le_one_of_le₀ (by linarith) (by positivity)
      _ ≤ e/2 := by field_simp
  · by_cases hL: L = 0
    · subst hL; field_simp; linarith
    calc
    _ = e/2 * (|L|/(|L| + 1)) := by field_simp
    _ ≤ e/2 * 1 := by gcongr; exact div_le_one_of_le₀ (by linarith) (by positivity)
    _ ≤ e/2 := by field_simp



theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  choose L ha using ha; choose M hb using hb
  rw [← Sequence.lim_eq]; convert tendsTo_mul ha hb
  <;> rw [lim_eq] at ha hb <;> simp_all


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
  rw [tendsTo_iff] at *; intro e he; specialize ha (e/(|c|+1)) (by positivity); choose N ha using ha
  use N; peel ha with n hn ha; simp; rw [← mul_sub_left_distrib]
  rw [abs_mul]
  calc
    _ ≤ |c| * (e / (|c| + 1)) := by gcongr
    _ = e * (|c| / (|c| + 1)) := by ring
    _ ≤ e * 1 := by gcongr; exact div_le_one_of_le₀ (by linarith) (by positivity)
    _ = e := by ring

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  choose L ha using ha
  rw [← Sequence.lim_eq]; convert tendsTo_smul c ha
  rw [lim_eq] at ha ; simp_all

instance Sequence.neg : Neg Sequence where
  neg a := {
    m := a.m
    seq n := -(a n)
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.neg_eval {a: Sequence} (n:ℤ) : (-a) n = -(a n) := rfl

theorem Sequence.neg_coe (a: ℕ → ℝ) : (-(a:Sequence)) = (fun n ↦ -(a n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

theorem Sequence.tendsTo_neg {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (-a).TendsTo (-L) := by
  rw [tendsTo_iff] at *; peel ha with e he N n hn ha
  convert ha using 1; rw [← neg_sub, abs_neg]; simp; congr 1; ring

theorem Sequence.lim_neg {a:Sequence} (ha: a.Convergent) :
    (-a).Convergent ∧ lim (-a) = -(lim a) := by
  choose L ha using ha
  rw [← Sequence.lim_eq]; convert tendsTo_neg ha
  rw [lim_eq] at ha; simp_all

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

theorem Sequence.sub_eq_add_neg (a b:Sequence) : a - b = a + (-b) := by
  ext n; rfl; simp; ring

/-- Theorem 6.1.19(d) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  rw [show L - M = L + (-M) by ring, sub_eq_add_neg]; convert tendsTo_add ha (tendsTo_neg hb)

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  rw [show lim a - lim b = lim a + (- lim b) by ring, sub_eq_add_neg]; convert lim_add ha (lim_neg hb).1
  apply (lim_neg hb).2.symm


noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

#check Sequence.IsCauchy.convergent

abbrev Sequence.EventuallyBoundedAwayZero (a: Sequence) : Prop :=
  ∃ (i : ℤ), ∃ (c:ℝ), c > 0 ∧ ∀ n ≥ i, |a n| ≥ c

theorem Sequence.boundedAwayZero_of_convergent_nonzero {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hL: L ≠ 0) :
    a.EventuallyBoundedAwayZero := by
  rw [tendsTo_iff] at ha; choose N ha using ha (|L/2|) (by positivity)
  refine ⟨N ,|L/2|, by positivity, ?_⟩; peel ha with n hn ha
  simp; rw [abs_sub_comm] at ha
  suffices |L/2|+ |L/2| ≤ |a n| + |L/2|  by linarith
  calc
    _ = |L| := by ring; rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]; ring
    _ ≤ |a n| + |L - a n| := by simpa [Real.dist_eq, abs_sub_comm] using (dist_triangle 0 (a n) L);
    _ ≤ |a n| + |L/2| := by simp [ha]



/-- Theorem 6.1.19(e) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  choose k A hA using boundedAwayZero_of_convergent_nonzero ha hnon
  choose i C hC hbound using boundedAwayZero_of_convergent_nonzero ha hnon
  rw [tendsTo_iff] at *; intro e he; choose j ha using ha (e * |L| * C) (by positivity)
  use max i (max j k); intro n hn; simp at hn
  have : 0 < |a n| := lt_of_lt_of_le hC (hbound n (by simp [hn]))
  have hnona: 0 ≠ a n := by aesop
  calc
    _ = |1/(a n) - 1/L| := by simp
    _ = |(L - a n) / (a n * L)| := by congr 1; field_simp [hnon];
    _ = |L - a n| / (|a n| * |L|) := by rw [abs_div, abs_mul]
    _ ≤ (e * |L| * C) / (C * |L|) := by gcongr;
                                        · rw [abs_sub_comm]; simp [ha, hn]
                                        · apply hbound; simp [hn]
    _ = e := by field_simp; ring
    _ ≤ e := by simp

#check Sequence.tendsTo_unique'

theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
    rw [← Sequence.lim_eq]; choose L ha using ha; convert tendsTo_inv (lim_def ⟨L,ha⟩) hnon


noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

theorem Sequence.div_eq_mul_inv (a b:Sequence) : a / b = a * b⁻¹ := by
  ext n; rfl; simp; ring

/-- Theorem 6.1.19(f) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  rw [show L / M = L * M⁻¹ by ring, div_eq_mul_inv]; convert tendsTo_mul ha (tendsTo_inv hb hnon)

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  rw [show lim a / lim b = lim a * (lim b)⁻¹ by ring, div_eq_mul_inv]; convert lim_mul ha (lim_inv hb hnon).1
  apply (lim_inv hb hnon).2.symm

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

theorem Sequence.eventually_le {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hLM: L < M) :
    ∃ N, ∀ n ≥ N, a n < b n := by
  rw [tendsTo_iff] at *; choose A ha using ha ((M-L)/3) (by linarith);
  choose B hb using hb ((M-L)/3) (by linarith); use max A B; intro n hn
  specialize ha n (by grind); specialize hb n (by grind)
  have : a.seq n ≤ L + (M-L)/3 := by linarith [le_abs_self (a n - L), ha]
  have : M - (M-L)/3 ≤ b.seq n := by linarith [neg_le_abs (b n - M), hb]
  linarith

/-- Theorem 6.1.19(g) (limit laws).  The `tendsTo` version is more usable than the `lim` version
    in applications. -/
theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  have hab := eventually_le ha hb; have hba:= eventually_le hb ha;
  rw [tendsTo_iff] at *; intro e he; specialize ha e he; specialize hb e he;
  choose A ha using ha; choose B hb using hb;
  simp;
  rcases lt_trichotomy L M with hLM | rfl | hLM
  · choose C hC using hab hLM;
    use max A (max B C); intro n hn; specialize ha n (by grind); specialize hb n (by grind);
    simpa [le_of_lt hLM, le_of_lt (hC n (by grind))]
  · use max A B; intro n hn; specialize ha n (by grind); specialize hb n (by grind);
    simp [max_def]; split_ifs <;> assumption
  · choose D hD using hba hLM
    use max A (max B D); intro n hn; specialize ha n (by grind); specialize hb n (by grind);
    simpa [le_of_lt hLM, le_of_lt (hD n (by grind))]

theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
    choose L ha using ha; choose M hb using hb
    rw [← Sequence.lim_eq]; convert tendsTo_max ha hb
    <;> rw [lim_eq] at ha hb <;> simp_all

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

lemma Sequence.neg_neg (a:Sequence) : - - a = a := by
  ext n; rfl; simp

lemma Sequence.min_neg_neg (a b:Sequence) : min (- a) (- b) = - max a b := by
  ext n; rfl; simp [← _root_.min_neg_neg];

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  rw [← neg_neg a, ← neg_neg b, ← _root_.neg_neg L, ← _root_.neg_neg M];
  rw [_root_.min_neg_neg, min_neg_neg]
  apply tendsTo_neg; apply tendsTo_max (tendsTo_neg ha) (tendsTo_neg hb)

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
    choose L ha using ha; choose M hb using hb
    rw [← Sequence.lim_eq]; convert tendsTo_min ha hb
    <;> rw [lim_eq] at ha hb <;> simp_all

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  induction' m with m ih
  · simp_all
  simp [Nat.lt_add_one_iff] at hnm
  rcases le_iff_lt_or_eq.mp hnm with hnm | rfl
  · specialize ih hnm; specialize ha m; linarith
  apply ha

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  rw [tendsTo_iff, tendsTo_iff]; peel with e he
  constructor <;> intro h <;> (choose N hN using h; use max N (max m a.m); intro n hn; simp at hn; specialize hN n hn.1)
  simpa [hn]; simpa [hn] using hN

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  rw [tendsTo_iff, tendsTo_iff]; peel with e he
  constructor <;> (rintro ⟨N, h⟩; use max (N+k) (a.m+k); intro n hn; simp at hn)
  · specialize h (n+k) (by grind); simpa [(by grind: a.m ≤ n)]
  specialize h (n-k) (by grind); simpa [(by grind: a.m ≤ n - k)] using h

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
  sorry

theorem Sequence.lim_const (r : ℝ ):
  ((fun _:ℕ ↦ r):Sequence).Convergent ∧ lim ((fun _:ℕ ↦ r):Sequence) = r := by
  rw [←lim_eq, tendsTo_iff]; intro ε hε; use 0; intro n hn; simp [hn]; linarith

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  use (fun _:ℕ  ↦  (1:ℝ)); use (fun (n:ℕ) ↦ (n+1:ℝ)⁻¹)
  refine ⟨(lim_const 1).1, Sequence.lim_harmonic.1, Sequence.lim_harmonic.2, ?_⟩
  rw [not_and_or]; left; simp_rw [convergent_def,tendsTo_iff ]; push_neg; intro L
  use 1; simp; intro N; choose n hn using exists_nat_gt L;
  use max (n+10) (N+10) ; refine ⟨by grind, ?_⟩;
  split_ifs with h; simp_all;
  · suffices ↑(max (↑n) N + 10).toNat > L by rw [abs_of_pos (by linarith)]; linarith
    apply lt_of_lt_of_le hn; simp; grind
  grind



theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  sorry
end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by sorry

end Chapter6
