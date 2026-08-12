import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1: b is a subsequence of a -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) :=
  ⟨(2*·), ⟨by intro m n hmn; simp_all, by intro n; rfl⟩⟩

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by
  intro i j hij; rcases lt_trichotomy i j with (h | rfl | h);
  · apply hf at h; linarith
  · rfl
  apply hf at h; linarith

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) :=
  ⟨(2*·), ⟨by intro m n hmn; simp_all, by intro n; simp⟩⟩

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  use fun n ↦ 2 * n + 1, fun m n hmn ↦ by dsimp; omega
  intro n
  simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
  congr 2; push_cast; omega

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  use (2*·+1); refine ⟨by intro m n hmn; simp; grind,?_⟩
  intro n; simp; grind -- Note: (n/2:ℤ) is integer division, so remainder is truncated

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a :=
  ⟨ (·), ⟨by intro m n hmn; simp_all,by intro n; rfl⟩ ⟩

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
  choose f hf1 hf2 using hab; choose g hg1 hg2 using hbc
  use f ∘ g; refine ⟨StrictMono.comp hf1 hg1, ?_⟩
  intro n; simp; rw [← hf2,← hg2]

theorem Sequence.strictmono_geq_linear {f:ℕ → ℕ} (hf: StrictMono f) : ∀n, f n ≥ n := by
  intro n; induction' n with n ih
  · apply Nat.zero_le
  specialize hf (a:= n) (b:= n+1) (by simp); linarith

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  refine ⟨?_, (· a (Sequence.subseq_self a))⟩
  intro h b ⟨f, hab1, hab2⟩; peel h with h e he; -- e for both sequences
  choose N hN1 hN2 using he; lift N to ℕ using hN1 -- Starting point N for sequence a
  refine ⟨N, by simp_all, ?_⟩ -- We'll use N for sequence b, because (b N) is at least as far along as (a N) **
  intro m hm; lift m to ℕ using (by simp_all; linarith); -- m ≥ N: indexing b
  have := strictmono_geq_linear hab1 m -- ** comes from this line: f m ≥ m
  specialize hN2 (f m) (by simp_all; linarith) -- m in b-space is (f m) in a-space
  convert hN2 using 1; simp_all; intro n; grind -- Clean up so they match




/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  constructor
  · intro h
    have key (n:ℕ): ∃ m, m > n ∧ |(a m) - L| ≤ 1/(n+1) := by -- Pick index that is close to L and later than n
      choose i hi1 hi2 using h (1/(n+1)) (by positivity) (n+1) (by positivity)
      simp at hi1; obtain ⟨hi3, hi4⟩ := hi1 -- 1/(n+1)-close, later than n_prev: index i
      lift i to ℕ using (by linarith); refine ⟨i, by linarith, ?_⟩ -- Using i
      simp_all; convert hi2 using 1; -- Match up TendsTo and LimitPoint (the same for the adhering points)

    let f : ℕ → ℕ := fun i ↦ Nat.rec (key 0).choose (fun n fn ↦ (key fn).choose ) i -- Each term must be later than previous
    use (fun i ↦ a (f i)) -- Function successfully constructed with desired properties
    have hf1 : StrictMono f := by
      apply strictMono_nat_of_lt_succ; intro n; apply (key (f n)).choose_spec.1; -- Each *consecutive* term is later --> strictmono

    constructor; refine ⟨f, hf1, by simp⟩
    intro e he; choose M hM using exists_nat_gt (1/e) -- Allowed our sequence to get arbitrary small with 1/(n+1)
    use M+1; refine ⟨by linarith, ?_⟩;
    intro i hi; simp at hi; lift i to ℕ using (by linarith); -- i ≥ M are e-close to L
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩ -- Turn i into k+1 so we can use recursive case
    obtain ⟨hi1, hi2⟩ := (by simpa using hi) -- Simplify
    simp [hi1, hi2, dist]; apply le_trans (key (f k)).choose_spec.2 -- Use recursive def
    suffices 1 / e ≤ (Nat.cast (f k) : ℝ) + 1 by simp_all; exact inv_le_of_inv_le₀ he this -- Rearrange
    apply (le_of_lt hM).trans;
    have := strictmono_geq_linear hf1 k; norm_cast; linarith -- Algebra for inequality

  rintro ⟨b, ⟨f, hf1, hf2⟩, hb⟩; intro e he N hN; lift N to ℕ using hN;  -- Setup: we want to get close to L at some point
  have := strictmono_geq_linear hf1 N -- (b N) will always be at least as far as (a N), so it's usable
  choose M hM0 hM using hb e he; lift M to ℕ using hM0; -- Get a point in the subsequence that is e-close to L
  specialize hM (max M N) (by simp_all); -- at least as far as N, but also e-close to L (at least at M)
  use f (max M N); have : N ≤ f (max M N) := by apply le_trans this; apply hf1.monotone; grind
  simp_all; grind -- Clean up and match b with a


/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
    apply isTrue; use fun n ↦ (-1)^n; use fun n ↦ (-1)^(n+1); constructor
    · rw [Function.ne_iff]; use 0; norm_num
    constructor
    · use fun n ↦ n+1; constructor; intro i j h; simp [h]
      intro n; simp
    use fun n ↦ n+1; constructor; intro i j h; simp [h]
    intro n; simp; rw [add_assoc]; rw [pow_add]; simp

#check Nat.find



lemma Sequence.finite_is_bounded (a:ℕ → ℝ) (N : ℕ) : ∃ M≥0, ∀ i ≤ N,  |a i| ≤ M := by
  induction' N with N ih; use |a 0|; simp;
  choose M hM1 hM2 using ih; use max M |a (N+1)|;
  simp; intro i hi; by_cases h: i = N+1
  · subst h; right; simp
  left; exact hM2 i (by omega);

/--
  Exercise 6.6.3.  You may find the API around Mathlib's `Nat.find` to be useful
  (and `open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  -- Structure is almost identical to Thm 6.6.6 proof where convenient
  have : ∀ N M, ∃ m > N, |a m| > M := by -- Later terms can get as large as we want
    unfold IsBounded BoundedBy at ha; push_neg at ha; contrapose! ha
    obtain ⟨N,M,hM⟩ := ha; obtain ⟨P,hP1, hP2⟩ := finite_is_bounded a N; use max M P;
    refine ⟨by simp; aesop, ?_⟩
    intro z; simp; by_cases h: ¬ 0 ≤ z
    · simp [h]; simp_all
    simp_all; by_cases h': z ≤ N
    · right; apply hP2; simp_all
    left; apply hM; simp_all
  have h n := this n n; -- Simplify to use Nat.rec
  let f : ℕ → ℕ := fun i ↦ Nat.rec (h 0).choose (fun n fn ↦ (h fn).choose) i
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ; intro n; apply (h (f n)).choose_spec.1
  use (fun n ↦ a (f n)); refine ⟨⟨f, hf, by simp_all⟩, ?_⟩
  -- We've gotten subsequence arbitrarily large. We show that its inverse gets arbitrarily small.
  intro e he; choose N hN using exists_nat_gt (1/e); -- Getting close to 0 with 1/(N+1)
  use N+1; refine ⟨by exact Int.le.intro_sub (N + 1 + 0) rfl, ?_⟩ -- Weird b/c ⁻¹ messes up a.m unfold
  intro i hi; lift i to ℕ using (by simp_all; linarith); -- i ≥ N + 1 gives us...
  simp at hi; obtain ⟨hi1, hi2⟩ := hi                     -- large enough terms
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩    -- nonzero terms
  simp_all; rw [if_pos (by linarith)]; apply inv_le_of_inv_le₀ he -- Rearranging
  -- N chosen to be as large as desired: 1/e < N. k chosen to exceed N.
  -- k forces f k to be as large. Thus, a(f(k+1)) is large enough for its inverse to approach 0.
  have h1:=  (h (f k)).choose_spec -- Can get arbitrarily high: higher than f k
  have h2:= strictmono_geq_linear hf k; -- We can control magnitude of f k with f k ≥ k
  -- e⁻¹ < N ≤ k ≤ f k < |a (f (k + 1))|
  apply (le_of_lt hN).trans; apply le_trans (b:= (k:ℝ)); simpa
  apply le_trans (b:=(Nat.cast (f k):ℝ)); simpa
  apply le_of_lt; apply h1.2


-- Here's the same theorem but with Nat.find instead, to get the spirit of
-- using the Well-Ordering Principle.
open Classical in
theorem Sequence.subseq_of_unbounded' {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  -- Structure is almost identical to Thm 6.6.6 proof where convenient
  have : ∀ N M, ∃ m > N, |a m| > M := by -- Later terms can get as large as we want
    unfold IsBounded BoundedBy at ha; push_neg at ha; contrapose! ha
    obtain ⟨N,M,hM⟩ := ha; obtain ⟨P,hP1, hP2⟩ := finite_is_bounded a N; use max M P;
    refine ⟨by simp; aesop, ?_⟩
    intro z; simp; by_cases h: ¬ 0 ≤ z
    · simp [h]; simp_all
    simp_all; by_cases h': z ≤ N
    · right; apply hP2; simp_all
    left; apply hM; simp_all
  have h n := this n n; -- Simplify to use Nat.rec
  let f : ℕ → ℕ := fun i ↦ Nat.rec (motive := fun _ => ℕ) (Nat.find (h 0)) (fun n fn ↦ Nat.find (h fn)) i
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ; intro n; apply (Nat.find_spec (h (f n))).1
  use (fun n ↦ a (f n)); refine ⟨⟨f, hf, by simp⟩, ?_⟩
  -- We've gotten subsequence arbitrarily large. We show that its inverse gets arbitrarily small.
  intro e he; choose N hN using exists_nat_gt (1/e); -- Getting close to 0 with 1/(N+1)
  use N+1; refine ⟨by simp [inv_coe]; linarith, ?_⟩
  intro i hi; lift i to ℕ using (by simp_all; linarith); -- i ≥ N + 1 gives us...
  simp at hi; obtain ⟨hi1, hi2⟩ := hi                     -- large enough terms
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩    -- nonzero terms
  simp_all; rw [if_pos (by linarith)]; apply inv_le_of_inv_le₀ he -- Rearranging
  -- N chosen to be as large as desired: 1/e < N. k chosen to exceed N.
  -- k forces f k to be as large. Thus, a(f(k+1)) is large enough for its inverse to approach 0.
  have h1:=  Nat.find_spec (h (f k)) -- Can get arbitrarily high: higher than f k
  have h2:= strictmono_geq_linear hf k; -- We can control magnitude of f k with f k ≥ k
  -- e⁻¹ < N ≤ k ≤ f k < |a (f (k + 1))|
  apply (le_of_lt hN).trans; apply le_trans (b:= (k:ℝ)); simpa
  apply le_trans (b:=(Nat.cast (f k):ℝ)); simpa
  apply le_of_lt; apply h1.2


end Chapter6
