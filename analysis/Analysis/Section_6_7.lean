import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real

lemma Sequence.neg_BoundedBy (a:Sequence) (M:ℝ) : a.BoundedBy M ↔ (-a).BoundedBy M := by
  constructor <;> intro h n <;> simpa using h n

lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  -- This proof is rearranged slightly from the original text.
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  by_cases h1 : x = 1
  · simp [h1]; exact ⟨ 1, lim_of_const 1 ⟩
  wlog h : 1 < x generalizing x α q -- x > 1 can use 1/x > 1. Just need -q to compensate
  · specialize this (x := 1/x) (α := -α) (q := -q) (by positivity)
      ((by convert tendsTo_neg hq; ext i; rfl; simp; grind))
      (by rw [neg_BoundedBy, neg_coe]; simpa) (by simp_all)
      (by simp_all; grind [one_lt_inv₀, lt_of_le_of_ne])
    convert this using 1; ext i; rfl; simp; split_ifs with h;
    rw [Real.inv_rpow, Real.rpow_neg, inv_inv]
    any_goals linarith
  have h': 1 ≤ x := by linarith
  rw [←Cauchy_iff_convergent]
  intro ε hε
  choose K hK hclose using lim_of_roots hx (ε*x^(-M)) (by positivity) -- x^(1/K) is (ε*x^(-M))-close to 1
  choose N hN hq using IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity) -- qn and qm are (1/K+1)-close
  simp [Real.CloseSeq, Real.dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose
  use N, by simp -- Start at N to make sure qn and qm are close
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm]) -- Specify (1/(K+1))-closeness
  simp [Real.Close, hn, hm, Real.dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  · replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [Real.rpow_le_rpow_left_iff h]; norm_cast -- Take qn and qm to exponent
    rw [abs_of_nonneg (by linarith)] -- Remove ineq
    calc -- First: extract x^(qm)
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←Real.rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by -- Turn into x^(qm) into x^M
        gcongr <;> try exact h'           -- and qn-qm into 1/(K+1)
        . rw [sub_nonneg]; apply Real.one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le'] -- Turn 1/(K+1) into ε*x^(-M)
      _ = ε := by rw [mul_comm, mul_assoc, ←Real.rpow_add]; simp; linarith -- Simp
  replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [Real.rpow_le_rpow_left_iff h]; norm_cast; linarith
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←Real.rpow_add]; ring_nf; positivity
    _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
      gcongr <;> try exact h'
      . rw [sub_nonneg]; apply Real.one_le_rpow h'; norm_cast; linarith
      . specialize hbound n; simp_all [abs_le']
      grind [abs_le']
    _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
    _ = ε := by rw [mul_comm, mul_assoc, ←Real.rpow_add]; simp; positivity

lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1 -- Functionally move q' to the other side
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))] -- Supposing x^rn converges to 1
    rw [lim_eq] at this -- This would allow us to do x^q = x^q'*x^(q-q')
    convert (lim_mul (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe] -- ...which is a provably true statement. Ta-da
      rcongr _ n
      rw [←Real.rpow_add (by linarith)]
      simp [r]
    grind
  /-
  I *think* this approach could have used 1/(K+1) without invoking a sequence at all
  But I think that would've required exists_nat_gt and also would've been more manual
  work. Annoying
  The fact that we're using it to isolate a singular value is why it isn't
  squeeze thm
  -/
  intro ε hε -- squeeze rn between 1/(K+1) and -1/(K+1) [not directly squeeze thm]
  have h1 := lim_of_roots hx -- Exponent form" x^(1/(K+1))
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε -- Need to get K1 and K2 (+ and -) separately
  choose K2 hK2 h4 using h2 ε hε
  clear h1 h2
  simp [Inv.inv] at hK1 hK2 -- cleanup
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2 -- We use max of both so we can use both properties
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])

  have hr := tendsTo_sub hq hq' -- rn between (+) and (-) needs convergence to 0
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity) -- N gets 1/(K+1)-close
  refine ⟨ N, by simp_all, ?_ ⟩

  intro n hn; simp at hn -- Pick n ≥ N, clean up
  simp [hn, Real.dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢ -- Both upper and lower bound of abs
  specialize hr n (by simp [hn]) -- 1/(K+1)-close, so it puts us within (+) (-)
  simp [Real.Close, hn, abs_le'] at hr

  obtain h | rfl | h := lt_trichotomy x 1 -- Order flips if we have x<1 instead of x>1
  · have h5 : x^(K + 1:ℝ)⁻¹ ≤ x ^ (r n.toNat:ℝ)  := by
      apply Real.rpow_le_rpow_of_exponent_ge ?_ ?_ -- Can't use gcongr, gotta flip
      simp_all [r]; all_goals linarith
    have h6 : x ^ (r n.toNat:ℝ) ≤ (x^(K + 1:ℝ)⁻¹)⁻¹  := by
      rw [←Real.rpow_neg (by linarith)];
      apply Real.rpow_le_rpow_of_exponent_ge ?_ ?_
      simp [r]; all_goals linarith
    split_ands <;> linarith
  · simp; linarith
  -- We get the inner fences using 1/(K+1) and -1/(K+1)
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←Real.rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  -- We already have the outer fences at 1-ε and 1+ε from the convergence of x^(1/(K+1)) and x^(-1/(K+1))
  split_ands <;> linarith

/- Reiterate ch5 construction of reals as limits of rational sequences, and use that
as a sequence we can always retrieve from any real number-/
theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q  -- Use the sequence q that constructs α in Chapter 5
  apply lim_eq_LIM at hcauchy -- This shows that that sequence converges to α
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy -- Clean up and remove the chapter 5 version of Reals
  convert hcauchy; aesop

-- Canonical sequence for a real
noncomputable abbrev Real.rSeq (α:ℝ) : ℕ → ℚ := (eq_lim_of_rat α).choose
noncomputable abbrev Real.rSeq_tendsTo (α:ℝ) := (eq_lim_of_rat α).choose_spec
/-
Use the canonical sequence for your exponent to create a canonical rpow sequence.
-/
noncomputable abbrev Real.rpow_seq (x:ℝ) (α:ℝ) := (fun n ↦ x^((rSeq α) n:ℝ))
/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim (Real.rpow_seq x α: Sequence)


/-
If another sequence converges to α, they create the same result when used as the exponent,
as the 'canonical' sequence we used for defining it.
In the textbook, this made the definition of "just choose some sequence that converges to α" well-defined.
While Lean has a *deterministic* choice operator, that was not assumed in the textbook.
This would be problematic for the textbook because we could create two non-equal objects
with the same definition, by using two slightly different (but both allowed) procedures.
-/
lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq
-- Convenient bonus: if we construct a sequence q' that converges to α, we can use that sequence
-- instead of some non-constructive choice we used in the definition.
-- That means we can do actually useful work with it, rather than having a
-- choice-defined object that isn't well-defined.

/-
Packages "your sequence converges" with "lim(your sequence) = rpow x α"

Together:

"your sequence converges to rpow x α"

Without the convergence, we don't know that the limit exists, so it could be a
'junk' value we don't care about.
-/
lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩



/-
The sequence used to construct rpow (rpow_seq) tends to rpow.

* Technically not free because rpow is just a limit: doesn't guarantee convergence.
* Moreover, we defined (eq_lim_of_rat q) as a convergent sequence,
* But we did NOT define rpow_seq as a convergent sequence: we just built it from one.

This lemma allows us to use rpow the way we expect to, by giving a license that says
'this is a valid limit'.
-/
--lemma Real.rpow_seq_tendsTo_rpow {x:ℝ} (hx: x > 0) {q:ℝ} :
--  (rpow_seq x q: Sequence).TendsTo (rpow x q) := by
--  -- Similar to ratPow_tendsto_rpow, we confirm convergence because
--  have hq := (eq_lim_of_rat q).choose_spec -- ... canonical q-sequence is convergent (by definition)
--  -- The main difference is the right part of ⟨,⟩ would be redundant:
--  rw [lim_eq]; exact ⟨ rpow_continuous hx, rfl⟩ -- rpow is already defined as the limit of rpow_seq

-- Being continuous is useful on its own, so we do that first

/-
Allows you to manipulate rpow terms as genuine limits
-/
lemma Real.rpow_continuous {x:ℝ} (hx: x > 0) {q:ℝ} :
  ((fun n ↦ x^((rSeq q) n:ℝ)):Sequence).Convergent := by
  exact ratPow_continuous hx (rSeq_tendsTo q)

lemma Real.rpow_seq_tendsTo_rpow {x:ℝ} (hx: x > 0) {q:ℝ} :
  (rpow_seq x q: Sequence).TendsTo (rpow x q) := lim_eq.mpr ⟨rpow_continuous hx, rfl⟩


/-
A somewhat stupid (and yet efficient) way to do it: directly use ratPow_tendsto_rpow machinery.
It'll do the continuous part for us, and the limit part...

In short: because rpow is using the same exponential sequence as itself,
that exp seq should converge to the same as itself. Thus, rpow's sequence converges
to the same as itself: rpow.

I guess you could say "they have the same structure (x ^ f n), plus
equivalent input sequences (f=q and f=q)".
And that's technically true for something with itself.
* "Identical objects are, in fact, in the same equivalence class".

[Really trying to force structure to make this make sense] The only 'difference' is,
one of the two copies of rpow has been privileged as "the thing other sequences converge to".
* This being the copy that was used earlier.
-/
lemma Real.rpow_seq_tendsTo_rpow' {x:ℝ} (hx: x > 0) {q:ℝ} :
  ((fun n ↦ x^((rSeq q) n:ℝ)):Sequence).TendsTo (rpow x q) :=
  ratPow_tendsto_rpow hx (rSeq_tendsTo q)




lemma Sequence.lim_of_const' (a:ℝ) : lim ((fun _:ℕ ↦ a):Sequence) = a :=
  (lim_eq.mp (lim_of_const a)).2

/-
Rational exponentiation is the same as real exponentiation when the exponent is rational:
not overloading notation with conflicting definitions.

* This is a bit tricky conceptually because Lean doesn't have a notion of (x:ℝ)^(q:ℚ)
* But the basic concept: (x:ℝ)^(q:ℚ) is a concrete number we already accept without rpow construction.

* So, is 'simple' (x:ℝ)^(q:ℚ) equal to the rpow version?
* Is it equivalent to use the simple version, or to turn q into its canonical sequence
* first, and then take the limit over that?

* Yes, because: we can replace rpow (using the canonical sequence) with the
* constant sequence (because q is rational, x^q is valid).

* We just get a bunch of copies of 'simple' x^q in the limit. Which... converges to x^q.

* In other words: no matter how annoying rpow is, we can just replace it with the simple
* version where we just use the rational exponentiation anyway.
-/
lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  -- Replace rpow's canonical q-sequence with the constant q-sequence.
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  -- Which creates a constant x^q sequence, converges to x^q.
  symm; apply Sequence.lim_of_const'

#check ge_of_tendsto

#check Sequence.inf_mono
#check Sequence.tendsTo_iff_eq_limsup_liminf'
#check Real.ratPow_tendsto_rpow

#check lim_def
#check inf_le_liminf

#check rpow_eq_lim_ratPow
#check lim_of_const

#check lim_add




/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  suffices inf (rpow_seq x q) ≥ 0 from ?_ -- inf ≤ liminf = lim
  · replace := (this).trans (inf_le_liminf _) -- inf ≤ liminf
    have hconverge := rpow_seq_tendsTo_rpow hx (q := q) -- (rpow x q) is a true limit
    rw [Sequence.tendsTo_iff_eq_limsup_liminf'] at hconverge; -- liminf = lim
    rw [hconverge.1] at this; simpa
  -- 0 ≤ all points → 0 ≤ inf
  apply inf_ge_lower; intro n hn; simp at hn; simp [hn, rpow_seq]; apply Real.rpow_nonneg; linarith

#check divergent_of_inv_zero



/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  conv at hq'r' => arg 1; arg 1; intro n; rw [← Rat.cast_add]
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←Real.rpow_add]; simp; linarith

lemma Real.ratPow_zero {x:ℝ} (hx: x > 0) : rpow x 0 = 1 := by
  rw [show (0:ℝ) = (0:ℚ) by simp, Real.rpow_of_rat_eq_ratPow hx]; simp

lemma Real.ratPow_one {x:ℝ} (hx: x > 0) : rpow x 1 = x := by
  rw [show (1:ℝ) = (1:ℚ) by simp, Real.rpow_of_rat_eq_ratPow hx]; simp



/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_pos {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q > 0 := by
  apply lt_of_le_of_ne (Real.ratPow_nonneg hx q); intro h
  have:= congr_arg (·*(rpow x (-q))) h; simp only [zero_mul] at this
  rw [← Real.ratPow_add hx] at this; simp only [add_neg_cancel] at this
  rw [Real.ratPow_zero hx] at this; linarith


#check lim_const
#check tendsTo_pow
#check tendsTo_inv
#check tendsTo_div

-------------------------EVENTUALLY EQUAL

abbrev Sequence.eventually_equal (a b:Sequence) := ∃ N, ∀ n ≥ N, a n = b n

abbrev Sequence.ee_symm : eventually_equal a b ↔ eventually_equal b a := by
  peel 3; grind

abbrev Sequence.positive (a:Sequence) := ∀ n ≥ a.m, a n > 0

lemma Sequence.ee_pos {a : Sequence} {A: ℝ} (ha:  a.TendsTo (A)) (hA: A > 0) :
  ∃ (a': Sequence), eventually_equal a a' ∧ positive a' ∧ a'.m = 0 := by
  use fun (n:ℕ) ↦ max (a n) (A/3);
  refine ⟨?_, by intro n hn; simp_all, rfl⟩
  choose N hN0 hN using ha (A/2) (by linarith); use max N 0;
  intro n hn; simp_all;
  specialize hN n (by grind); simp [dist,abs_le'] at hN
  rw [if_pos (by grind)] at hN; linarith



noncomputable abbrev Sequence.pos_seq {a:Sequence} {A: ℝ} (ha:  a.TendsTo (A)) (hA: A > 0):=
  (Sequence.ee_pos ha hA).choose

lemma Sequence.pos_seq_prop {a : Sequence} {A: ℝ} (ha:  a.TendsTo (A)) (hA: A > 0) :
  eventually_equal a (pos_seq ha hA) ∧ positive (pos_seq ha hA) ∧ (pos_seq ha hA).m = 0 :=
  (Sequence.ee_pos ha hA).choose_spec


theorem Sequence.tendsTo_of_eventually_eq {a b : Sequence} {L : ℝ}
    (h: eventually_equal a b) (ha : a.TendsTo L) : b.TendsTo L := by
  peel ha with e he ha; -- Distance e
  choose N hN using h; obtain ⟨M, ⟨h1,h2⟩⟩ := ha -- Get min indices for equality + distance
  use max N (max M b.m); simp -- Also make sure to be above b.m
  peel h2 with n h2 -- Now, we show they're equivalent
  intro hna; convert h2 (by grind) using 1
  simp_all

lemma Sequence.ee_pos_tendsTo {a : Sequence} {A: ℝ} (ha:  a.TendsTo (A)) (hA: A > 0) :
  (pos_seq ha hA).TendsTo (A) := by apply tendsTo_of_eventually_eq (pos_seq_prop ha hA).1 ha




-------------------------END


lemma Sequence.tendsTo_intPow {a : Sequence} {L:ℝ} (ha: a.TendsTo L) (hL: L > 0) :
∀ k:ℤ, ((fun (n:ℕ) ↦ (a n)^(k:ℝ):Sequence)).TendsTo (L^(k:ℝ)) := by
  intro k; by_cases hk: k ≥ 0 -- Directly maps onto ℕ theorem tendsTo_pow
  · lift k to ℕ using hk; simp; have := tendsTo_pow ha k
    apply Sequence.tendsTo_of_eventually_eq ?_ this
    use max 0 a.m; intro n hn; simp_all;
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩ -- Need inv first
  simp_all; rw [← inv_coe, ← fun_pow]
  apply tendsTo_inv ?_ (by positivity)
  apply tendsTo_pow;
  apply Sequence.tendsTo_of_eventually_eq ?_ ha
  use max 0 a.m; intro n hn; simp_all

lemma Sequence.convergent_of_tendsTo {a:Sequence} {R: ℝ} (h: a.TendsTo (R)) : a.Convergent :=
⟨R, h⟩


lemma Real.nonneg_sequence_for_nonneg_real {x:ℝ} (hx: x ≥ 0) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo x ∧ ∀ n, 0 ≤ q n := by
  choose q hq using eq_lim_of_rat x
  by_cases h0: x = 0 -- In the 0 case, we need absolute, but it's easy to simplify
  · refine ⟨fun n ↦ |q n|, ?_, by aesop⟩
    subst h0; rw [Sequence.tendsTo_zero_iff] at hq; convert hq
    ext i; simp; by_cases h0: i ≥ 0 <;> simp [h0]
  replace hx := hx.lt_of_ne' h0 -- In the x>0 case, we can just use the sequence from the positive point
  choose N hN using Sequence.eventually_le (Sequence.tendsTo_const 0) hq hx
  rw [Sequence.tendsTo_of_from N] at hq
  refine ⟨fun n ↦ if N ≤ (n:ℤ) then q n else 0, ?_, ?_⟩ -- Writing out the `from` sequence sucked
  · rw [Sequence.tendsTo_of_from N]; convert hq using 1; ext i -- Equivalent sequences
    simp; by_cases h:  0 ≤ i ∧ N ≤ i <;> simp [h]
  intro n; by_cases h: N ≤ (n:ℤ) <;> simp [h]; -- All nonnegative by construction
  specialize hN n h; simp_all [show 0 ≤ (n:ℤ) by linarith]
  linarith

lemma Real.ge_sequence_for_ge_rat {C : ℚ} {x:ℝ} (hx: x ≥ C):
∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo x ∧ ∀ n, C ≤ q n := by
  choose q hq1 hq2 using nonneg_sequence_for_nonneg_real (x := x - C) (by linarith)
  use fun n ↦ q n + C; split_ands -- Replace x - C ≥ 0 with x ≥ C
  · convert tendsTo_add hq1 (tendsTo_const C) <;>
    simp [add_coe]
  simpa


#check lim_smul

lemma Sequence.eventually_positive {A:ℝ } {a: Sequence} (ha: a.TendsTo (A)) (hA: A > 0) :
∃ N, ∀ n ≥ N, a.seq n > 0 := by
  rw [Sequence.tendsTo_iff] at ha
  choose N ha using ha (A/2) (by linarith)
  exact ⟨N, fun n hn => by have := ha n hn; rw [abs_le] at this; linarith⟩

lemma Sequence.eventually_gt {A B:ℝ } {a: Sequence} (ha: a.TendsTo (A)) (hA: A > B):
∃ N, ∀ n ≥ N, a.seq n > B := by
  rw [Sequence.tendsTo_iff] at ha
  choose N ha using ha ((A - B)/2) (by linarith)
  exact ⟨N, fun n hn => by have := ha n hn; rw [abs_le] at this; linarith⟩


/-
Needed because Lean gets fussy about the difference between a sequence vs when
we do the simplified ℕ → ℚ version -/
lemma Sequence.tendsTo_natseq {A: ℝ} {a: Sequence} (ha: a.TendsTo A):
  ((fun (m:ℕ) ↦ (a m:ℝ)):Sequence).TendsTo (A) := by
  apply Sequence.tendsTo_of_eventually_eq ?_ ha
  use max 0 a.m; intro m hm; simp_all;




lemma Sequence.substitute_base_with_ee {a a' b : Sequence} {L : ℝ}
    (h: eventually_equal a a') (ha : ((fun (n:ℕ) ↦ (a n:ℝ)^(b n:ℝ)):Sequence).TendsTo L):
    ((fun (n:ℕ) ↦ (a' n:ℝ)^(b n:ℝ)):Sequence).TendsTo L := by
  intro ε hε; choose N hN using h; choose M hM0 hM using ha ε hε -- ee and ε conditions
  use max N M; simp_all; intro n hn; specialize hN n (by grind)
  specialize hM n (by grind); convert hM using 1; simp_all

lemma Sequence.substitute_base_with_ee' {a a' : Sequence} {b: ℕ → ℚ } {L : ℝ}
    (h: eventually_equal a a') (ha : ((fun (n:ℕ) ↦ (a n:ℝ)^(b n:ℝ)):Sequence).TendsTo L):
    ((fun (n:ℕ) ↦ (a' n:ℝ)^(b n:ℝ)):Sequence).TendsTo L := by
  intro ε hε; choose N hN using h; choose M hM0 hM using ha ε hε -- ee and ε conditions
  use max N M; simp_all; intro n hn; specialize hN n (by grind)
  specialize hM n (by grind); convert hM using 1; simp_all

/-
If both terms converge, and the base converges to 1, the whole thing converges to 1
-/
lemma Sequence.tendsTo_one_pow' {B: ℝ} {a: Sequence} {b: ℕ → ℚ} (ha: a.TendsTo 1) (hb: ((fun n ↦ (b n:ℝ)):Sequence).TendsTo B):
  ((fun (n:ℕ) ↦ (a n:ℝ)^(b n:ℝ)):Sequence).TendsTo (1) := by
  -- Set up a' for positivity (retrieval)
  have ⟨hee,hplus,h0⟩ := pos_seq_prop ha (by norm_num)
  apply substitute_base_with_ee' (ee_symm.1 hee)
  have ha' := ee_pos_tendsTo ha (by norm_num)
  set a' := pos_seq ha (by norm_num)
  -- Bounding b n so we can get a squeeze (retrieval)
  choose M hM0 hM using bounded_of_convergent (convergent_of_tendsTo hb)
  unfold BoundedBy at hM; choose Z hMZ using exists_int_gt M
  -- Setting up the functions I use for my squeeze theorem: a'^(Z) and a'^(-Z) (retrieval)
  have hZ := tendsTo_intPow ha' (by norm_num) Z;
  have hnZ := tendsTo_intPow ha' (by norm_num) (-Z)
  have hhigh := tendsTo_max hZ hnZ -- Max and min covers the cases where a' ≥ 1 or a' < 1
  have hlow := tendsTo_min hZ hnZ
  simp [Real.rpow_intCast, one_zpow] at hhigh hlow
  apply lim_of_between (by simp [inst_min, inst_max]) ?_ hlow hhigh;
  -- Select index, prep for final proving (processing)
  intro n hn; simp [inst_min] at hn; simp [hn]
  specialize hM n; simp [abs_le', hn] at hM
  have hbz:= lt_of_le_of_lt hM.1 hMZ;
  have hbz':= lt_of_le_of_lt hM.2 hMZ
  repeat rw [← Real.rpow_intCast]
  -- Turn inequalities into power inequalities (computing)
  by_cases h1: a'.seq n ≥ 1
  · refine ⟨by right; gcongr; apply h1; grind, by left; gcongr; apply h1⟩ --gcongr solves
  simp at h1; specialize hplus n (by grind)
  constructor --gcongr doesn't handle reversed case
  · left; apply Real.rpow_le_rpow_of_exponent_ge <;> linarith
  right; apply Real.rpow_le_rpow_of_exponent_ge <;> linarith


lemma Sequence.tendsTo_ratPow' {A B: ℝ} {a: Sequence} {b : ℕ → ℚ} (hA: A > 0)
(ha: a.TendsTo A) (hb: ((fun n ↦ (b n:ℝ)):Sequence).TendsTo B):
  ((fun (n:ℕ) ↦ (a n:ℝ)^(b n:ℝ)):Sequence).TendsTo (rpow A B) := by
  -- Set up a' for positivity (retrieval)
  have ⟨hee,hplus,h0⟩ := pos_seq_prop ha hA
  set a' := pos_seq ha hA
  -- Divide both sides by A^(b n) (processing)
  let v : Sequence := fun (n:ℕ) ↦ (a' n / A)
  let u : ℕ → ℝ := fun (n:ℕ) ↦ (v n) ^ (b n:ℝ)
  suffices (fun (n:ℕ) ↦ (v n) ^ (b n:ℝ) : Sequence ).TendsTo (1) from ?_
  · apply substitute_base_with_ee' (ee_symm.1 hee)
    apply tendsTo_mul (ratPow_tendsto_rpow hA hb) at this; simp only [mul_one] at this
    convert this; rw [mul_coe]; ext i; simp
    by_cases hi: i ≥ 0 <;> simp [hi]
    unfold v; simp [hi]; rw [Real.div_rpow ?_ (by linarith)]; field_simp;
    · specialize hplus i (by linarith); linarith
  -- If v tends to 1, then v^(b n) (computing)
  apply tendsTo_one_pow' ?_ hb
  unfold v; rw [show 1=A/A by grind, ← div_coe];
  apply Sequence.tendsTo_div ?_ (tendsTo_const A) (by linarith)
  exact tendsTo_natseq (tendsTo_of_eventually_eq hee ha)




#check Real.rpow_seq_tendsTo_rpow

/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by
  choose p hp using eq_lim_of_rat q
  choose s hs using eq_lim_of_rat r
  have hx_q:= Real.ratPow_tendsto_rpow hx hp
  have hx_q_r := Sequence.tendsTo_ratPow' (ratPow_pos hx q) hx_q hs
  rw [lim_eq] at hx_q_r; rw [← hx_q_r.2] -- left side
  have hps := tendsTo_mul hp hs; rw [mul_coe] at hps
  conv at hps => arg 1; arg 1; intro n; rw [← Rat.cast_mul]
  rw [ rpow_eq_lim_ratPow hx hps]
  congr; ext i; simp; rw [Real.rpow_mul (by linarith)]




/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  choose q' hq' using eq_lim_of_rat q
  have hqneg := (neg_coe _) ▸ (tendsTo_neg hq')
  conv at hqneg => arg 1; arg 1; intro n; rw [← Rat.cast_neg]
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hqneg]
  simp only [one_div]; apply eq_inv_of_mul_eq_one_right

  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hqneg
  rw [← (lim_mul h1 h2).2, mul_coe];

  convert lim_of_const' (1:ℝ) with i;
  rw [← Real.rpow_add (by linarith)]; simp;




lemma Sequence.lim_sub {a b : Sequence} (ha : a.Convergent) (hb : b.Convergent) :
  (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  have hbneg:= Sequence.lim_neg hb
  rw [sub_eq_add_neg, _root_.sub_eq_add_neg, ← hbneg.2]
  apply lim_add ha hbneg.1

lemma Sequence.lim_nonneg_mono {b:Sequence} (h: ∀ n, 0 ≤ b n) (hb: b.Convergent) :
0 ≤ lim b := by
  contrapose! h; have hb' := lim_def hb
  rw [tendsTo_iff_eq_limsup_liminf'] at hb'
  choose N hN0 hN using Sequence.gt_limsup_bounds (x:= 0) (a := b) (by rw [hb'.2]; aesop)
  use N; specialize hN N (by simp); aesop


lemma Sequence.lim_mono {a b:Sequence} (h: ∀ n, a n ≤ b n) (ha: a.Convergent) (hb: b.Convergent) :
lim a ≤ lim b := by
  have hsub:= Sequence.lim_sub hb ha
  rw [← sub_nonneg, ← hsub.2]
  apply lim_nonneg_mono (by simpa) hsub.1

lemma Real.ratPow_le_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) (hxy : x ≤ y): rpow x q ≤ rpow y q := by
  choose p hp1 hp2 using Real.nonneg_sequence_for_nonneg_real (le_of_lt h)
  rw [Real.rpow_eq_lim_ratPow hx hp1, Real.rpow_eq_lim_ratPow hy hp1]
  apply lim_mono ?_ (ratPow_continuous hx hp1) (ratPow_continuous hy hp1)
  intro n; by_cases h0 : n ≥ 0 <;> simp [h0];
  gcongr; aesop

/-- Proposition 6.7.3(d) / Exercise 6.7.1 -/
theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  have := (ratPow_le_mono hx hy h).mt; simp at this
  constructor <;> intro hxy
  · -- split > goal into ≠ and ≤, then use ratPow_le_mono to get the ≤ part
    apply lt_of_le_of_ne (by apply ratPow_le_mono hy hx h; exact le_of_lt hxy);
    contrapose! hxy; apply le_of_eq
    have := congr_arg ((rpow · (1/q))) hxy; simp only at this;
    rw [ratPow_ratPow hy, ratPow_ratPow hx] at this
    field_simp at this; symm
    rwa [Real.ratPow_one hy, Real.ratPow_one hx] at this;
  contrapose! hxy; exact ratPow_le_mono hx hy h hxy

#check Real.rpow_pos_of_pos

lemma Real.one_ratPow  (x:ℝ): rpow 1 x = 1 := by
  nth_rw 2 [← lim_of_const' 1]; unfold rpow;
  choose p hp using eq_lim_of_rat x
  congr; ext n; simp

theorem Real.ratPow_mono_of_gt_one' {x:ℝ} (hx: x > 1) {q r:ℝ} (h : q > r) : rpow x q > rpow x r := by
  choose p hp using eq_lim_of_rat q -- (retrieval)
  choose s hs using eq_lim_of_rat r
  suffices rpow x (q-r) > 1 from ?_ -- (processing)
  · rw [show q-r = q+-r by ring, Real.ratPow_add (by linarith)] at this
    rw [Real.ratPow_neg (x:=x) (by linarith) r] at this
    rw [mul_one_div, gt_iff_lt] at this;
    rw [lt_div_iff₀ (by apply ratPow_pos (by linarith))] at this; simp_all;
  rw [← one_ratPow (q-r), ← ratPow_mono]; -- (computing)
  all_goals linarith

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  choose p hp using eq_lim_of_rat q -- (retrieval)
  choose s hs using eq_lim_of_rat r
  refine ⟨?_, Real.ratPow_mono_of_gt_one' hx⟩;
  contrapose!; intro h;
  rcases lt_or_eq_of_le h with (h | rfl);
  · apply le_of_lt; exact ratPow_mono_of_gt_one' hx h
  rfl

#check ratPow_neg
#check ratPow_ratPow

/-
Algebra rearrangement to get ⁻¹ out of the rpow expression.
-/
theorem Real.inv_ratPow {x:ℝ} (hx: x > 0) {q:ℝ} : rpow (x⁻¹) q = (rpow x q)⁻¹ := by
  rw [← zpow_neg_one x]
  rw [show x^(-1:ℤ)=x^((-1:ℚ):ℝ) from (Real.rpow_intCast x (-1)).symm]
  rw [← rpow_of_rat_eq_ratPow hx]
  rw [ratPow_ratPow hx]
  rw [mul_comm]
  rw [← ratPow_ratPow hx]
  rw [rpow_of_rat_eq_ratPow (ratPow_pos hx q)]
  simp only [Rat.cast_neg, Rat.cast_one];
  exact Real.rpow_neg_one (rpow x q)



/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q > rpow x r ↔ q < r := by
  obtain ⟨x, rfl⟩ : ∃ y, x = y⁻¹ := by use x⁻¹; field_simp;
  rw [inv_pos] at hx0; rw [inv_lt_one₀ hx0] at hx; simp_all
  repeat rw [inv_ratPow hx0]
  rw [inv_lt_inv₀ (ratPow_pos hx0 r) (ratPow_pos hx0 q) ]
  exact ratPow_mono_of_gt_one hx

/-- Proposition 6.7.3(f) / Exercise 6.7.1 -/
theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  choose p hp using eq_lim_of_rat q -- (retrieval)
  have h1 := ratPow_tendsto_rpow hx hp
  have h2 := ratPow_tendsto_rpow hy hp
  have hxy := ratPow_tendsto_rpow (mul_pos hx hy) hp
  rw [lim_eq] at h1 h2 hxy; rw [← h1.2, ← h2.2, ← hxy.2]
  have hxy' := lim_mul h1.1 h2.1
  rw [← hxy'.2, mul_coe] -- (processing)
  congr; ext i; apply Real.mul_rpow (by linarith) (by linarith) -- (computing)

end Chapter6
