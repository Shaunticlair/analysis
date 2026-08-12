import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (_:ℕ) ↦ c):Sequence).TendsTo c := by
  intro e he; use 0; simp; intro n hn; simp_all; linarith

/-
Tao defines exponentiation over a sequence: each elem gets exponentiated
-/

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0 -- Couldn't this just be a n ^ k?
    vanish := by grind
  }

-- We unpack to allow pow to pass in/out of the sequence.

@[simp]
lemma Sequence.pow_eval {a:Sequence} {k: ℕ} {n: ℤ} (hn : n ≥ a.m): (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow]; simp; rw [Pow.pow, inst_pow]; simp only
  grind

-- Usually pow laws applied to the sequence directly, rather than elementwise.

lemma Sequence.fun_pow (f:ℕ → ℝ) (k:ℕ): ((f:Sequence))^k = ((fun n ↦ f n ^ k) : Sequence) := by
  ext n; rfl; simp; split_ifs with h;
  · rw [pow_eval (by positivity)]; simp_all;
  apply Sequence.vanish; simp at h; convert h

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ): a^(k+1) = a^k * a := by
  ext x
  · symm; exact Int.min_self a.m
  · simp only [mul_eval]
    by_cases h: x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    · simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha'; grind -- Inductive is entirely handled by lim_mul
  have hlim : (lim a)^(k+1) = 0 := by -- lim = 0 b/c a^(k+1) = 1/(n+1) and lim_harmonic = 0
    rw [←(hpow k).2]; convert lim_harmonic.2; ext i; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h <;> simp -- Ugly work to cancel exps
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    convert Real.rpow_one _; field_simp
  simp [lim_eq, ha', pow_eq_zero hlim]

#check Sequence.lim_of_between

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  by_cases h0: x = 0;
  · subst h0; intro e he; use 1; simp; intro n hn; simp_all [show 0 ≤ n from by grind];
    convert le_of_lt he; simp; linarith
  have habs : ((fun (n:ℕ) ↦ |x|^n):Sequence).TendsTo 0 := by
    rw [lim_eq]; apply (lim_of_exp (by simp [h0]) (by grind))
  apply lim_of_between (a:= fun n ↦ -|x|^n) (c:= fun n ↦ |x|^n) (by grind) ?_ ?_ habs
  · intro n hn; simp_all; constructor <;> rw [pow_abs]; apply neg_abs_le; apply le_abs_self
  · convert tendsTo_neg habs; ext i; rfl; aesop; simp


/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  subst hx; convert lim_of_const 1; aesop

#check Sequence.lim_eq
lemma Sequence.lim_eq' {a:Sequence} (ha: a.Convergent) : ∃ L, lim a = L := by
  choose r hr using ha; use r; rw [lim_eq] at hr; exact hr.2

#check Sequence.lim_const
-- There's a version where you don't assume a i ≠ 0 (using 'bounded away from 0'), but I don't want to prove that right now.
lemma Sequence.divergent_of_inv_zero {a: ℕ → ℝ} (ha: (a: Sequence).TendsTo 0)
(ha': ∀ n, a n ≠ 0) :
((fun n ↦ 1/a n): Sequence).Divergent := by
  rw [lim_eq] at ha -- lim a = 0
  obtain ⟨ha_conv, ha_lim⟩ := ha
  intro ⟨L, hL⟩; rw [lim_eq] at hL -- lim 1/a = L
  obtain ⟨hL_conv, hL_lim⟩ := hL
  obtain ⟨h1_conv, h1_lim⟩ := (lim_const 1) -- lim 1 = 1

  have ⟨hmul_conv, hmul_lim⟩ := lim_mul ha_conv hL_conv -- lim a*(1/a) = 0
  rw [ha_lim, hL_lim, zero_mul] at hmul_lim; -- But also, lim a*(1/a) = lim 1 = 1
  suffices (1:ℝ) = 0 by linarith -- Thus, we derive our contradiction
  rw [← h1_lim, ← hmul_lim]
  congr; ext i; rfl; simp
  by_cases h: i ≥ 0 <;> simp [h]
  rw [CommGroupWithZero.mul_inv_cancel ]; simp; apply ha'


/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
  rcases hx with rfl | hx
  · unfold Divergent; rw [← Cauchy_iff_convergent]; exact ex6_1_13
  conv => arg 1; arg 1; intro n; rw [show x^n = 1/(1/x)^n by ring_nf; rw [inv_inv]]
  apply divergent_of_inv_zero (lim_of_geometric (x := 1/x) ?_)
  intro n; simp; rintro rfl; norm_num at hx
  · rw [abs_div]; simp; exact inv_lt_one_of_one_lt₀ hx



theorem Sequence.not_bddAbove_of_divergent_of_monotone {a:Sequence} (ha: a.Divergent) (hmono: a.IsMonotone) : ¬ a.BddAbove := by
  contrapose! ha; convert convergent_of_monotone ha hmono; grind -- Contrapose

lemma Sequence.pow_pos_monotone {x:ℝ} (hx: x > 1) : ((fun (n:ℕ) ↦ x^n):Sequence).IsMonotone := by
  intro n hn; simp_all; rw [if_pos (by linarith)];
  refine pow_le_pow_right₀ ?_ ?_; linarith; aesop

lemma Sequence.lt_one_plus_pow (x e: ℝ ) (he : e > 0) : ∃ (n:ℕ), x < (1+e)^(n+1:ℝ) := by
  have hdiv := lim_of_geometric'' (x:=1+e) (by right; rw [abs_of_pos ?_] <;> linarith)
  have := not_bddAbove_of_divergent_of_monotone hdiv (Sequence.pow_pos_monotone (by linarith))
  contrapose! this; use x; intro n hn; lift n to ℕ using (by aesop)
  simp; apply le_trans ?_ (this n);
  rw [← Real.rpow_natCast]; gcongr <;> linarith

lemma Sequence.lim_of_roots' {x:ℝ} (hx: x > 1) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  rw [tendsTo_iff]; intro e he;
  choose N hN using Sequence.lt_one_plus_pow x e he; use N;
  intro n hn; simp; rw [if_pos (by linarith)]

  rw [abs_of_pos ?_]
  simp; rw [Real.rpow_inv_le_iff_of_pos]
  apply le_of_lt; apply lt_of_lt_of_le hN
  rw [add_comm]; gcongr
  (any_goals rw [Int.le_toNat]); rotate_right
  · simp; rw [Real.lt_rpow_inv_iff_of_pos]; simp; apply hx
    any_goals linarith
  any_goals linarith

#check Sequence.lim_const


/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · have := convergent_of_monotone (a:= ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence)) ?h1 ?h2
    choose L hL using this; convert hL -- Our seq has limit L; we want limit 1 (L=1)
    have := lim_of_roots' (x := 1/x) (one_lt_one_div hx h) -- Inverse seq has limit 1
    have hL' := mul_coe _ _ ▸ tendsTo_mul hL this; rw [mul_one] at hL' -- Mul has limit L
    apply Sequence.tendsTo_unique' _ ?_ hL' -- We want mul limit = 1
    convert tendsTo_const 1 with n -- Prove self*inv = 1
    rw [← Real.mul_rpow, mul_one_div, div_self]; simp -- w/ some algebra
    any_goals positivity -- Handle side conditions
    · use 1; intro n hn; simp_all; -- Bounded above by 1: x<1, x^i<1^i
      apply le_of_lt; rw [Real.rpow_inv_lt_iff_of_pos]; simp [h]; any_goals linarith
    · intro n hn; simp_all; rw [if_pos]; -- Monotone: 1/n decrease, so 1/n^x increase
      apply Real.rpow_le_rpow_of_exponent_ge -- Compare exponents
      (any_goals linarith); gcongr; simp -- Cleanup
  · simp; apply tendsTo_const
  apply lim_of_roots' (by linarith)

#check Sequence.lim_of_power_decay

theorem Sequence.tendsTo_pow {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
∀ k:ℕ, (a^k).TendsTo (L^k) := by
  intro k; induction' k with k ih
  · rw [tendsTo_iff]; intro e he; use max 0 a.m; intro n hn;
    rw [pow_eval]; simp; linarith; simp; aesop
  rw [Sequence.pow_succ, _root_.pow_succ];
  apply tendsTo_mul ih ha

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
  rw [← Rat.num_div_den q]; simp; -- First, extract q.num
  conv => arg 1; arg 1; intro n; rw [← Real.inv_rpow (by linarith), div_eq_inv_mul, Real.rpow_mul (by positivity)]
  simp; (have : q.num > 0 := by aesop); set k := q.num; clear_value k; lift k to ℕ using (by linarith)
  simp; rw [show (0:ℝ) = 0^k by rw [zero_pow (by linarith)]]
  rw [← Sequence.fun_pow]; apply Sequence.tendsTo_pow -- q.num is irrelevant if the inside equals 0
  conv => arg 1; arg 1; intro n; repeat rw [← one_div]

  choose m hm using Nat.exists_eq_add_one_of_ne_zero (q.den_nz) -- Now, convert to match theorem
  rw [hm]; simp only [Nat.cast_add, Nat.cast_one] -- Need m+1 form (positive exponent)
  convert Sequence.lim_of_power_decay (k:=m) using 1 -- Theorem
  congr; funext n; simp; rw [Real.inv_rpow (by positivity)]; -- Move around exponent


/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
  conv => arg 1; arg 1; intro n; rw [← inv_inv ((n + 1: ℝ ) ^ (q:ℝ)), ← one_div, ← one_div]
  apply Sequence.divergent_of_inv_zero (Sequence.lim_of_rat_power_decay (q:=q) hq)
  intro n; apply one_div_ne_zero; rw [Real.rpow_ne_zero];
  (any_goals linarith); aesop

end Chapter6
