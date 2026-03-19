import Mathlib.Tactic
import Analysis.Section_5_4
import Analysis.Section_4_4

set_option linter.unusedVariables false
/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  rw [Real.upperBound_def]
  constructor <;> intro h
  · apply h 1 (by rw [Real.mem_Icc]; norm_num)
  · intro x hx; rw [Real.mem_Icc] at hx; linarith

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M, M ∈ upperBounds (.Ioi (0:Real)) := by
  push_neg; intro M;
  rw [Real.upperBound_def, Real.Ioi_def];
  push_neg; use max (M+1) 1; simp

lemma upper_empty : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M; rw [Real.upperBound_def]; intro x hx; contradiction

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := upper_empty

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  rw [Real.upperBound_def] at *; peel hb with  _ _ hxm;
  apply le_trans hxm h

/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1:Real) := by
  rw [Real.isLUB_def, Real.upperBound_def, Real.Icc_def];
  constructor
  · intro x hx; simp at hx; exact hx.2
  · intro M hM; rw [Real.upperBound_def] at hM; apply hM 1 (by simp)



/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  intro h; choose M hM using h; rw [Real.isLUB_def, Real.upperBound_def] at hM;
  obtain ⟨ _, hM ⟩ := hM; -- M-1 will be a lesser upper bound than M
  specialize hM (M-1) (upper_empty (M-1)); linarith -- No possible "least" UB

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by grind [Real.isLUB_def] -- M ≤ M' and M' ≤ M

/-- definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

lemma Real.upper_vs_nonupper {E: Set Real} {x y: Real}
  (hupper: x ∈ upperBounds E) (hnupper: y ∉ upperBounds E) : y < x := by
  rw [Real.upperBound_def] at *;
  push_neg at hnupper; choose z he h1 using hnupper
  specialize hupper z he; linarith

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: (K*(1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: (L*(1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  have : n+1 > 0 := by positivity
  have : ((1/(n + 1):ℚ):Real) > 0 := by positivity
  by_contra! h
  -- If we can't ever cross over from non-upper bound to upper bound,
  -- Any amount we add to L still won't be an upper bound
  have hnupper: ∀ (x : ℕ ), ((L+x)*((1/(n+1)):ℚ):Real) ∉ upperBounds E := by
    intro x;
    induction' x with x ih
    · simp_all
    · -- We know L + x + 1 fits into the (L, K] range
      have := upper_vs_nonupper hK ih
      have : (L+x:Real) < K := by nlinarith
      have : L + x <   K    := by exact_mod_cast this
      have : L + x + 1 ≤ K  := by linarith
      -- Thus, we cannot have L + x below the bound, and L + x + 1 above it
      specialize h (L+x+1) (by linarith) (by linarith)
      -- Meaning: if L + x is not an upper bound, then neither is L + x + 1
      have h := mt h
      conv at h => lhs; arg 1; arg 2; arg 1; simp
      -- And we already know by induction that L + x is not an upper bound
      specialize h ih
      convert h; simp; rw [add_assoc]

  -- This means we can never exceed K either, since K *is* an upper bound
  have hcontra : ∀ (x : ℕ), x < (K-L) := by
    intro x; specialize hnupper x
    have heq := upper_vs_nonupper hK hnupper;
    suffices (L + x : Real) < K  by norm_cast at *; linarith
    nlinarith
  -- This is, of course, absurd: we can simply choose x = K-L
  specialize hcontra ((K-L).toNat); contrapose! hcontra; simp

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
(hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
(hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
(hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
(hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
m = m' := by
  by_contra! hne
  wlog hlt : m < m' -- Flipping m and m' doesn't matter
  · exact this hm'1 hm'2 hm1 hm2 (Ne.symm hne) (by push_neg at hlt; omega)
  -- 1. If m' greater, then m can only be as large as m'-1
  have hmm': m ≤ m' - 1 := by linarith
  -- 2. But if m/(n+1) is an upper bound, that makes (m'-1)/(n+1) one, too
  apply hm'2; --Which is a contradiction
  refine (Real.upperBound_upper ?_ hm1)
  -- Cleanup work for the obvious link: m-1 ≤ m → m/(n+1) ≤ (m'-1)/(n+1)
  have h0: (n+1:Real) > 0 := by positivity
  push_cast; field_simp
  rw [div_le_div_iff₀ h0 h0]; field_simp
  exact_mod_cast hmm'


/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe] at *; peel ha with e he N j hj k hk h
  rw [Section_4_3.dist_eq] at *
  refine le_trans (by apply abs_abs_sub_abs_le_abs_sub) h

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  rw [LIM_eq_LIM ha hb] at h;
  rw [LIM_eq_LIM (Sequence.IsCauchy.abs ha) (Sequence.IsCauchy.abs hb)]
  rw [Sequence.equiv_iff] at *
  peel h with e he N n hn h
  apply le_trans (by apply abs_abs_sub_abs_le_abs_sub) h

lemma Rat.dist_le_iff (ε a b : ℚ) : |a - b| ≤ ε ↔ b - ε ≤ a ∧ a ≤ b + ε := by
  exact_mod_cast Real.dist_le_iff ε a b

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
LIM a = LIM |a| := by
  rw [← isPos_iff, Real.isPos_def] at h
  choose b hbound hb heq using h
  choose B hBpos hbB using hbound
  rw [heq, Real.LIM.abs_eq ha hb heq]
  congr; ext n; simp; rw [abs_of_nonneg];
  specialize hbB n; linarith


theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  have habs := Sequence.IsCauchy.abs ha
  have haneg := Sequence.IsCauchy.neg _ ha
  rcases Real.trichotomous' (LIM a) 0 with ( hpos | hneg | heq)
  · rw [_root_.abs_of_pos hpos]; apply Real.LIM.abs_eq_pos hpos ha
  · rw [_root_.abs_of_neg hneg];
    have : LIM (-a) > 0 := by rw [← neg_LIM _ ha]; linarith
    rw [neg_LIM _ ha, show (|a| = |-a|) by simp];
    apply Real.LIM.abs_eq_pos this haneg
  · rw [abs_of_nonneg (by linarith), heq];
    rw [← LIM.zero,LIM_eq_LIM, Sequence.equiv_iff] at *;
    peel heq with e he N n hN h; simp_all;
    any_goals apply (Sequence.IsCauchy.const 0);
    apply ha; apply habs

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
(h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
  choose N hN using h
  set b := Real.truncated_seq N (a N) a -- Use truncated sequence
  have hbcauchy := truncated_seq_isCauchy N (a N) a hcauchy
  rw [truncated_seq_eq_LIM N (a N) a hcauchy]
  apply Real.LIM_of_le hbcauchy; intro n
  unfold Real.truncated_seq;
  by_cases hn : n < N <;> simp [hn]
  · exact hN N (by linarith)
  · exact hN n (by linarith)

#check Real.LIM_of_le

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy' {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
(q:Sequence).IsCauchy:= by
  -- If our terms can be 1/M close, they can be arbitrarily close (by increasing M)
  rw [Sequence.IsCauchy.coe]; intro e he
  choose N hN using exists_nat_gt (1/e);
  have hN : 0 < N + 1 := by positivity
  have h : 1 / e ≤ (N:Real) + 1 := by linarith
  have h: 1 / (N + 1) ≤ e := by
    rw [div_le_iff₀ (by norm_cast)] at *; rw [mul_comm]; exact_mod_cast h
  specialize hq N; use N; intro j hj k hk
  specialize hq j hj k hk
  rw [Section_4_3.dist]; linarith


theorem Real.LIM_of_Cauchy'' {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
∀ M, |q M - LIM q| ≤ 1 / (M+1):= by
  -- We know that n,m are trapped within 1/(M+1) of each other for n,m ≥ M
  have hqcauchy := Real.LIM_of_Cauchy' hq
  -- So, we know that any q n must be trapped that close to q M
  peel hq with M hq; specialize hq M (by linarith)
  -- Grab cauchy properties
  have hqconst := Sequence.IsCauchy.const (q M)
  have hqsub := Sequence.IsCauchy.sub hqconst hqcauchy
  have hqabs := Sequence.IsCauchy.abs hqsub
  -- For q M to be close to LIM q, that means the limit of their difference must be small
  -- More precisely, the limit of the distance between q n and q M must be small
  rw [ratCast_def, LIM_sub hqconst hqcauchy, LIM_abs hqsub];
  -- We know the limit is small if every term is small
  apply LIM_of_le' hqabs
  -- But our premise already gives us that q n and q M are close together
  use M; peel hq with n hn h
  rw [show (1/(M+1):Real) = ((1/(M+1):ℚ):Real) by simp]
  rw [Rat.cast_le (K := Real)]
  convert h

/-
Sketch of an alternative proof that might be closer to what
was intended, based on the description the textbook gives:
q M - 1/(M+1) ≤ q n ≤ q M + 1/(M+1)
Use LIM_mono on these to get
q M - 1/(M+1) ≤ LIM q ≤  q M + 1/(M+1)

Or some more technically correct version of this, idk I'm
not implementing it
-/


theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := ⟨ Real.LIM_of_Cauchy' hq, Real.LIM_of_Cauchy'' hq ⟩

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE -- Grab an element of E
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real) -- All our terms include a 1/(n+1) factor
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  · -- Take even increments of 1/(n+1), and find the crossing point to upper bounds
    rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M -- K * ε is an upper bound increment
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by -- L * ε is NOT an upper bound increment
      rw [Real.upperBound_def]; push_neg; use x₀;
    have claim1_3 : (K:Real) > (L:Real) := by -- Thus, L < K
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    -- We previously found a crossing point m between L and K
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      · qify; rwa [←gt_iff_lt, gt_of_coe]
      · simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m -- Use crossing point
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp -- Convert formatting
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  · -- We previously proved uniqueness of such m
    grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    -- The basic concept: because a n and a n' both straddle the upper bound by a
    -- tiny amount, they can't be too far apart
    intro n hn n' hn'
    -- In particular, adding/subtracting a small amount to either will cause them
    -- to cross over each other
    -- Each of these operations show that one can't be too big or too small
    -- Otherwise, the gap would be too large to be crossed so easily
    rw [abs_le]
    -- We break this into two cases, accounting for which of a n or a n' is larger
    split_ands
    · ---- a n can't be too much smaller: if we add only a small amount, it beats a n'
      specialize hm1 n; specialize hm2 n'; specialize hb n'
      -- x is an upper bound and y isn't →  x > y
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      -- Since we're beyond 1/(N+1), we can use that as a simplifying bound
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [Pi.sub_apply] at bound1; linarith
    · ---- a n can't be too much larger: if we subtract a small amount, it loses to a n'
      specialize hm1 n'; specialize hm2 n
      have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
      have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
      linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- Our goal is to fence in the sup above and below by multiples of ε
  -- Which can then be tightened to a single value by increasing n
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  -- We retrieve the crossing-over discrete value m for each n
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  -- We divide by n+1 to get desired upper bound approximations
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have hb : (b:Sequence).IsCauchy := .harmonic'
  -- Properties of a n (and, consequently, m n)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  -- Our discretized approximation of the upper bound gets arbitrarily close together
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2 -- a n and a n' close by 1/(N+1)
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  -- LIM a = LIM (a-b) is our candidate for the least upper bound
  -- a and a-b fence in our sup from above and below, arbitrarily closely
  set S := LIM a; use S -- a will allow us to prove it's an upper bound
  -- We know that it's an arbitrarily close fence, because they converge to the same value
  have claim4 : S = LIM (a - b) := by -- (a-b) will allow us to prove it's the LEAST upper bound
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  · -- All terms of (a) are upper bounds, so LIM a is an upper bound
    intros; apply LIM_of_ge claim3; grind [upperBound_def]
  · -- All terms of (a-b) are ≤ any upper bound, so LIM (a-b) is ≤ any upper bound
    intro y hy
    have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
    rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers ⊤ to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers ⊥ to denote the -∞ element.-/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]



/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two' : ∃ x:Real, x > 0 ∧ x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  -- Bounding sup E : 1 ≤ sup E ≤ 2
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos;
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real) -- Important: sup E is a real number
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  -- We also know that it's positive
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  -- We'll show that sup E ^ 2 = 2 by ruling out <2 and >2
  -- If sup E^2 was away from 2, then there's a gap between 2 and sup E^2
  -- Thus, there's an amount that we could nudge it closer to 2, without crossing over
  -- But then, this close value will either violate the upper bound or the least-ness
  use x; obtain h | h | h := trichotomous' (x^2) 2
  · -- First case: x^2 > 2
    exfalso; rw [isLUB_def] at claim3; have claim3 := claim3.2
    absurd claim3; push_neg
    -- Our goal is to find ε that gives (x-ε)^2 > 2: shows x^2 isn't the LEAST upper bound
    suffices ∃ e, e > 0 ∧ e < 1 ∧ (x - e)^2 > 2 by
      choose e he1 he2 he3 using this; use (x-e); simp [he1]
      have why (y:Real) (hy: y ∈ E) : x - e ≥ y := by
        simp [E] at hy
        have : (x-e)^2 ≥ y^2 := by linarith
        contrapose! this; -- (x-e)^2 < y^2 → x-e < y if both nonnegative
        apply pow_lt_pow_left₀ this (by linarith) (by norm_num)
      rwa [upperBound_def]

    -- Expand (x-e)^2
    conv => arg 1; intro e; rw [show (x - e)^2 = x^2 - 2*x*e + e^2 by ring]
    -- Since x^2 > 2, we know that we can subtract a small amount to get above 2
    -- We just want x^2 - C*e: so, we'll lower-bound (x - e)^2 to get a term like this
    -- Specifically: lower-bound e^2 → 0, and lower-bound 2*x*e → 2*2*e
    suffices ∃ e, e > 0 ∧ e < 1 ∧ x^2 - 4*e + 0 > 2 by
      choose e he1 he2 he3 using this; refine ⟨ e, he1, he2, ?_ ⟩;
      apply lt_of_lt_of_le he3;
      gcongr; linarith; nlinarith
    -- x^2 - 4*e > 2 → e < (x^2-2)/4 (thus, (x^2-2)/8 is sufficient)
    -- e < 1 (thus, 1/2 is sufficient)
    -- These are both upper bounds, so we take the minimum of both
    set e := min (1/2) ((x^2-2)/8)
    refine ⟨e, by simp [e, h], by simp [e]; left; norm_num, ?_⟩
    observe he: e ≤ (x^2-2)/8
    linarith

  · -- This is a more-or-less equivalent argument: preserving Tao's original form
    have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  · -- Third case: the correct case
    refine ⟨by linarith,by assumption⟩

theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 :=
  ⟨exist_sqrt_two'.choose, exist_sqrt_two'.choose_spec.2⟩

noncomputable abbrev Real.sqrt2 := Real.exist_sqrt_two'.choose

abbrev Real.sqrt2_prop :sqrt2 > 0 ∧ sqrt2^2 = 2:= Real.exist_sqrt_two'.choose_spec


lemma Real.sqrt2_irrational: ¬ ∃ q:ℚ, sqrt2 = (q:Real) := by
  have := Rat.not_exist_sqrt_two -- We already showed no (q:ℚ)^2=2
  have hsqrt := sqrt2_prop.2
  intro h; choose q hq using h; rw [hq] at hsqrt
  apply this; use q; push_neg at this
  exact_mod_cast hsqrt

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := ⟨sqrt2, sqrt2_irrational⟩

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

theorem Real.mem_lowerBounds_neg (E: Set Real) (x:Real) :
    x ∈ lowerBounds (-E) ↔ -x ∈ upperBounds E := by
  rw [lowerBound_def, upperBound_def];
  constructor <;>
    (intro h z hz; specialize h (-z);
     simp at *; specialize h hz; linarith)

theorem Real.mem_upperBounds_neg (E: Set Real) (x:Real) :
    x ∈ upperBounds (-E) ↔ -x ∈ lowerBounds E := by
  rw [lowerBound_def, upperBound_def];
  constructor <;>
    (intro h z hz; specialize h (-z);
     simp at *; specialize h hz; linarith)

lemma Real.forall_negative (x : Real) (P: Real → Prop):
  (∀ x, P x) ↔ (∀ x, P (-x)) := by
  constructor <;> (intro hy y; specialize hy (-y); convert hy); ring

lemma Real.exists_negative (x : Real) (P: Real → Prop):
  (∃ x, P x) ↔ (∃ x, P (-x)) := by
  constructor <;> (intro hy; choose y hy using hy; use -y); convert hy; ring

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  simp_rw [isGLB_def, isLUB_def, mem_lowerBounds_neg] at *
  rw [forall_negative]; convert h using 1 <;> simp; apply 2 -- Literally no idea why Lean wants an arbitary Real here. Nonemptiness maybe?


theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  rw [exists_negative]; simp_rw [← isLUB_neg]; choose e he using hE
  convert LUB_exist (⟨-e, by simp [he]⟩) (BddBelow.neg hbound); use 0

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

-- A little bit of language for irrationals
abbrev Real.IsIrrational (x:Real) : Prop := ¬ ∃ q:ℚ, x = (q:Real)

lemma Real.exist_irrational' : ∃ x:Real, Real.IsIrrational x := Real.exist_irrational

lemma Real.irrational_plus_rational {x:Real} (hx: Real.IsIrrational x) (q:ℚ) :
    Real.IsIrrational (x + (q:Real)) := by
  contrapose! hx; push_neg at *; choose p hp using hx
  use p-q; simp; linarith

lemma Real.irrational_times_rational {x:Real} (hx: Real.IsIrrational x) (q:ℚ) (hq: q ≠ 0) :
    Real.IsIrrational (x * (q:Real)) := by
  contrapose! hx; push_neg at *; choose p hp using hx
  use p/q; field_simp [hp]

#check Real.sqrt2_irrational
#check Real.sqrt2_prop
/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
  choose a ha using rat_between hxy
  choose b hb using rat_between ha.2
  conv => arg 1; intro z; arg 2; arg 2; change Real.IsIrrational (z)
  use a + (sqrt2)*(1/2 :ℚ)*(b-a);
  and_intros
  · apply lt_trans ha.1; simp [Real.sqrt2_prop.1];
    rw [lt_of_coe]; linarith
  · suffices sqrt2 *(1/2) * (b-a) < b-a by linarith
    suffices sqrt2*(1/2) < 1 by simp_all
    suffices sqrt2 < 2 by linarith
    rw [← pow_lt_pow_iff_left₀ (n := 2) _ (by simp) (by simp)]
    linarith [Real.sqrt2_prop.2]; linarith [sqrt2_prop.1]
  rw [add_comm, ratCast_sub]
  apply irrational_plus_rational;
  apply irrational_times_rational _ _
  · suffices (b:Real)-(a:Real) ≠ 0 by exact_mod_cast this
    linarith
  apply irrational_times_rational _ _ (by simp)
  exact sqrt2_irrational

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the `sSup` operation to build a conditionally complete lattice structure on `Real`-/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
