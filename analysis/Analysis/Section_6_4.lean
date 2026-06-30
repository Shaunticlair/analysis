import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/


abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    peel with e he N hN n; constructor <;> rintro ⟨h1, h2⟩
    · simp at h1; simp [h1]; simp [Real.Close, dist] at h2; convert h2; simp [h1.1, h1.2]
    simpa [dist, h1, (by linarith : a.m ≤ n)]

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  use 0; unfold Example_6_4_3; simp [dist]; rw [abs_of_pos ?_]; norm_num; norm_num



/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  unfold Example_6_4_3 Real.ContinuallyAdherent Real.Adherent; push_neg;
  use 1; simp; intro z hz; simp [hz, show 0 ≤ z by linarith, dist]
  have : (10:ℝ)^(-z-1) < 1*(10)^(-(1:ℤ)) := by rw [one_mul]; gcongr; simp; linarith
  rw [abs_of_pos]; norm_num at *; linarith
  · suffices (10:ℝ)^(-z-1) < 2*(10)^(-(1:ℤ)) by norm_num at *; linarith
    apply lt_trans this; gcongr; norm_num

lemma zero_point_one : (0.1:ℝ) = (10:ℝ)^(-1:ℤ) := by norm_num

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro N hN; use N; simp [hN]; rw [zero_point_one]; gcongr; simp; linarith

#check Chapter5.ten_pow_geq

lemma exists_ten_pow_geq (x:ℝ) : ∃ n, x ≤ 10^n := by
  choose n h using exists_nat_gt x; use n
  linarith [show (n:ℝ ) ≤ 10^(n) by exact_mod_cast (Chapter5.ten_pow_geq  n)]

lemma exists_ten_pow_leq (x:ℝ) (hx : x > 0) : ∃ n:ℕ, 10^(-(n:ℤ)) ≤ x := by
  choose n h using exists_ten_pow_geq (1/x); use (n)
  field_simp; refine (one_div_le (by positivity) hx).mpr h


/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  intro e he; choose z hz using exists_ten_pow_leq e he
  intro N hN; simp at hN; use max N z; unfold Example_6_4_3
  simp [hN]
  apply le_trans ?_ hz; gcongr; simp; simp; grind

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  use 0; simp; norm_num

lemma neg_one_pow_mul_cancel (n:ℕ) (x:ℝ) : |(-1:ℝ)^n * x| = |x| := by simp [abs_mul, abs_pow];

#check neg_one_pow_eq_or

lemma inv_eq_pow_neg_one (x:ℝ) : x⁻¹ = x^(-(1:ℤ)) := by simp



/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  intro N hN; simp at hN; use 2*N; simp [hN, dist, show N ≤ 2*N by linarith]
  rw [Int.toNat_mul (by positivity) (by positivity)]; simp
  rw [abs_of_pos (by positivity), zero_point_one]; gcongr; simp; linarith


/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  intro e he; choose z hz using exists_ten_pow_leq e he
  intro N hN; use max (2*N) (2*z); simp [hN, (by linarith : N ≤ 2*N), dist];
  rw [show max (2*N) (2*z) = 2*(max N z) by grind]; rw [Int.toNat_mul (by positivity) (by positivity)]
  simp; rw [abs_of_nonneg (by positivity)]; apply le_trans ?_ hz; gcongr; simp; simp; grind

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  intro e he; choose z hz using exists_ten_pow_leq e he
  intro N hN; use (2 * max N z) + 1; simp [hN, dist]; refine ⟨by grind, ?_⟩
  simp [show N ≤ 2 * max N ↑z + 1 by grind, show 0 ≤ 2 * max N ↑z + 1 by grind]
  rw [Int.toNat_add (by positivity) (by positivity), Int.toNat_mul (by positivity) (by positivity), pow_add];
  simp; rw [abs_of_nonneg (by positivity)]; apply le_trans ?_ hz; gcongr; simp; ring_nf; simp; grind

#check neg_one_pow_eq_or

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  rw [Sequence.limit_point_def, Example_6_4_4]; push_neg; use 0.1; norm_num; use 0; norm_num
  intro z hz; simp [hz]; rcases neg_one_pow_eq_or (R:=ℝ) z.toNat with (h | h)
  <;> rw [h] <;> simp <;>
  [rw [abs_of_pos (by positivity)]; (rw [abs_of_neg (by ring_nf; rw [← neg_pos]; simp; positivity )]; simp;)]
  <;> (apply lt_trans (b := 1) (by norm_num); simp; positivity)

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  rw [Sequence.limit_point_def, tendsTo_iff] at *; peel h with e he h
  intro N hN; choose M h using h; use max N M; simp; apply h; simp

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }



noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

lemma E647_bddAbove : Example_6_4_7.BddAbove := by
  use (2:ℝ); unfold Example_6_4_7; intro n hn; simp at hn; simp [hn]
  rcases neg_one_pow_eq_or (R:=ℝ) n.toNat with (h | h) <;> rw [h] <;> simp
  apply le_trans (b:= 1 + 1) (by simp; linarith); norm_num; norm_num;
  apply le_trans (b:= 0) (by simp; positivity); norm_num

lemma Ex647up (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
  unfold Example_6_4_7 Sequence.upperseq; set f := ((fun (n:ℕ) ↦ (-1: ℝ) ^ n * (1 + 10 ^ (-(n:ℤ) - 1))):Sequence)
  apply le_antisymm
  · apply Sequence.sup_le_upper; intro z hz; simp at hz; simp [f, hz]; obtain ⟨hz1,hz2⟩:= hz
    rcases Nat.even_or_odd z.toNat with (h | h) <;> simp [h] <;>
    split_ifs with hN <;> simp; gcongr; simp;
    (have : (n:ℤ ) ≠ z := by intro hz; simp [← hz] at h; grind); replace hz2 : (n:ℤ) < z := by order
    apply add_le_add_left; norm_cast; simp_all; linarith
    all_goals apply le_trans (b:=0); simp; positivity; positivity
  split_ifs with h
  · apply le_trans ?_ (Sequence.le_sup (n:=n ) (a:=f.from ↑n) (by simp [f]))
    simp [f, h]
  apply le_trans ?_ (Sequence.le_sup (n:=n+1 ) (a:=f.from ↑n) (by simp [f]));
  have : Even (n+1) := by grind
  simp [f, show (0:ℤ) ≤ n + 1 by grind, this]; apply add_le_add_left; simp; linarith

#check EReal.real_of_not_top_bot

example : Example_6_4_7.limsup = 1 := by
  unfold Sequence.limsup; rw [← isGLB_iff_sInf_eq]; constructor <;> simp [lowerBounds, upperBounds]
  · intro x z hz; lift z to ℕ using hz; rw [Ex647up z]; rintro rfl
    split_ifs with h; all_goals norm_cast; simp; positivity
  intro x hx; contrapose! hx; let e := x - 1;
  rw [show  x = 1 + e by simp [e]; rw [add_comm, ← EReal.coe_one, EReal.sub_add_cancel]] at *
  by_cases h : e = ⊤ ; use Example_6_4_7.upperseq (0:ℕ); use (0:ℕ); rw [Ex647up 0, h]; simp;

  exact
    compareOfLessAndEq_eq_lt.mp rfl
  choose r hr using EReal.real_of_not_top_bot e (by aesop)
  rw [hr, ← EReal.coe_one] at hx; norm_cast at hx; simp at hx;
  choose n hn using exists_ten_pow_leq r hx
  use Example_6_4_7.upperseq (2*n); use 2*n; simp; rw [show 2*(n:ℤ) = (2*n:ℕ) by norm_cast, Ex647up (2*n)]
  simp [show Even (2*n) by grind, hr]; norm_cast; simp;
  apply lt_of_lt_of_le (by gcongr; simp; linarith) hn

lemma EReal.coe_neg_one : ( (-1):ℝ) = (-1: EReal) := by rfl;
lemma EReal.sub_eq_add_neg (x y : EReal) : x - y = x + (-y) := by rfl

lemma Ex647down (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  unfold Example_6_4_7 Sequence.lowerseq; set f := ((fun (n:ℕ) ↦ (-1: ℝ) ^ n * (1 + 10 ^ (-(n:ℤ) - 1))):Sequence)
  apply le_antisymm
  · split_ifs with h
    · apply le_trans (Sequence.ge_inf (n:=n+1 ) (a:=f.from (n)) (by simp [f]));
      simp [f,h, show (0:ℤ) ≤ n + 1 by omega]; gcongr; simp; linarith
    apply le_trans (Sequence.ge_inf (n:=n ) (a:=f.from (n)) (by simp [f]))
    simp [f, show Odd n by grind]
  apply Sequence.inf_ge_lower; intro z hz; simp at hz; simp [f, hz]; obtain ⟨hz1,hz2⟩:= hz
  rcases Nat.even_or_odd z.toNat with (h | h) <;> simp [h] <;>
  split_ifs with hN <;> simp <;> rw [← EReal.coe_one] <;> norm_cast
  any_goals try gcongr; any_goals try (apply le_trans (b:=0); simp; positivity)
  any_goals try norm_num;
  linarith [show n < z by apply lt_of_le_of_ne hz2 (by grind)]; assumption



#check EReal.bot_lt_coe

example : Example_6_4_7.liminf = -1 := by
  unfold Sequence.liminf; rw [← isLUB_iff_sSup_eq]; constructor <;> simp [lowerBounds, upperBounds]
  · intro r z hz; lift z to ℕ using hz; rw [Ex647down z]; rintro rfl;
    split_ifs with h; all_goals (rw [show (-1:EReal) = (-1:Real) by simp];  norm_cast; simp; positivity)
  intro r hx; contrapose! hx; let e := -1 - r
  rw [show r = -1 - e by simp [e]; rw [← EReal.coe_neg_one, EReal.sub_eq_add_neg _ r, EReal.sub_add_cancel_left]; simp] at *
  by_cases h : e = ⊤; use Example_6_4_7.lowerseq (0:ℕ); use (0:ℕ); rw [Ex647down 0]; simp [h];
  constructor <;> norm_cast
  choose r hr using EReal.real_of_not_top_bot e (by simp [h]; intro h; simp [h] at hx; norm_cast)
  rw [hr, ← EReal.coe_one] at hx; norm_cast at hx; simp at hx;
  choose n hn using exists_ten_pow_leq r hx;
  use Example_6_4_7.lowerseq (2*n+1); use (2*n+1); simp; norm_cast; rw [Ex647down (2*n+1)]
  refine ⟨by omega, ?_⟩; simp; rw [hr, ← EReal.coe_one]; norm_cast; simp; ring_nf
  rw [neg_lt_neg_iff]; apply lt_of_lt_of_le (by gcongr; simp; linarith) hn


example : Example_6_4_7.sup = (1.1:ℝ) := by
  unfold Sequence.sup; apply le_antisymm
  · apply csSup_le (Sequence.nonempty _); intro b hb; simp at hb; choose z hz h using hb; lift z to ℕ using hz
    subst h; simp; rcases neg_one_pow_eq_or (R:=EReal) z with (h|h) <;> rw [h] <;> simp
    norm_cast; apply le_trans (b:= 1 + 10^(-(1:ℤ ))); gcongr; simp; linarith; norm_num
    apply le_trans (b:=0); simp; positivity; norm_num
  suffices (1.1:ℝ) = Example_6_4_7 0 by rw [this]; apply Sequence.le_sup (by simp)
  unfold Example_6_4_7; simp; norm_num

example : Example_6_4_7.inf = (-1.01:ℝ) := by
  unfold Sequence.inf; apply le_antisymm
  · suffices (-1.01:ℝ) = Example_6_4_7 1 by rw [this]; apply Sequence.ge_inf (by simp)
    unfold Example_6_4_7; simp; norm_num
  apply le_csInf (Sequence.nonempty _); intro b hb; simp at hb; choose z hz h using hb; lift z to ℕ using hz
  subst h; simp; rcases Nat.even_or_odd z with (h|h) <;> simp [h]
  apply le_trans (b:=0); simp; norm_num; positivity; have : z ≥ 1 := by grind
  norm_cast; apply (le_trans (b:= 1 + 10^(-(2:ℤ )))); gcongr; simp; linarith; norm_num

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)


lemma Example_6_4_8_upperseq (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by
  unfold Sequence.upperseq; rw [sSup_eq_top]; intro b hb;
  by_cases h: b = ⊥;
  · use 2*n+1; simp [h]; constructor; use (2*(n:ℤ));
    simp [show (n:ℤ) ≤ 2*n by linarith, show Even (2*(n:ℤ)).toNat by grind]; norm_cast
    constructor <;> exact compareOfLessAndEq_eq_lt.mp rfl
  choose r hr using EReal.real_of_not_top_bot b (by aesop)
  choose m hm using exists_nat_gt r; use (Example_6_4_8.from ↑n) (2*(m+n));
  constructor; use (2*(m+n)); simp; grind
  · rw [hr]; simp; split_ifs with h1 h2 h3;
    rw [Int.toNat_mul (by positivity) (by positivity), Int.toNat_add (by positivity) (by positivity)]; simp; linarith; all_goals grind -- Remove contradictory cases

example : Example_6_4_8.limsup = ⊤ := by
  unfold Sequence.limsup; simp [sInf_eq_top]; intro r z hz ; lift z to ℕ using hz; rintro rfl
  apply Example_6_4_8_upperseq

lemma Example_6_4_8_lowerseq (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by
  unfold Sequence.lowerseq; rw [sInf_eq_bot]; intro b hb;
  by_cases h: b = ⊤;
  · rw [h]; use ((Example_6_4_8.from ↑n) (2*n:ℕ)); constructor
    · use (2*n); constructor; simp; linarith; rfl
    · exact EReal.coe_lt_top ((Example_6_4_8.from ↑n).seq ↑(2 * n))
  obtain ⟨r,rfl⟩ := EReal.real_of_not_top_bot b (by aesop)
  by_cases hr: r ≥ 0
  · use (Example_6_4_8.from ↑n) (2*n+1: ℕ); constructor
    · use (2*n+1: ℕ); constructor; simp; linarith; rfl
    · simp; split_ifs with h1 h2 h3; swap
      rw [Int.toNat_add (by positivity) (by positivity), Int.toNat_mul (by positivity) (by positivity)]; simp; linarith; grind; grind; contrapose! h1; linarith
  choose m hm using exists_nat_gt (-r); use (Example_6_4_8.from ↑n) (2*(m+n)+1: ℕ); constructor
  · use (2*(m+n)+1: ℕ); constructor; simp; linarith; rfl
  simp; split_ifs with h1 h2 h3; swap
  rw [Int.toNat_add (by positivity) (by positivity), Int.toNat_mul (by positivity) (by positivity)];
  rw [Int.toNat_add (by positivity) (by positivity)]
  simp; linarith; grind; grind; contrapose! h1; linarith


example : Example_6_4_8.liminf = ⊥ := by
  unfold Sequence.liminf; simp [sSup_eq_bot]; intro r z hz ; lift z to ℕ using hz; rintro rfl
  exact Example_6_4_8_lowerseq z

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

lemma Ex649u (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ := by
  unfold Sequence.upperseq; apply le_antisymm
  · apply Sequence.sup_le_upper; intro z hz; simp at hz; simp [hz]; simp [show 0 ≤ z by linarith]
    lift z to ℕ using (by linarith); split_ifs with h1 h2; gcongr; exact_mod_cast hz
    any_goals apply le_trans (b:=0); simp; positivity; positivity
    replace hz := by simpa using lt_of_le_of_ne hz (by grind)
    · simp; gcongr 1; norm_cast; linarith
  split_ifs with h <;> [convert (Sequence.le_sup (n:=n) ?_); convert (Sequence.le_sup (n:=n+1) ?_)]
  (any_goals unfold Example_6_4_9; simp [h]); split_ifs with h1 h2; all_goals grind

lemma Ex649ls : Example_6_4_9.limsup = 0 := by
  unfold Sequence.limsup; rw [← isGLB_iff_sInf_eq]; constructor <;> simp [lowerBounds, upperBounds]
  · intro r z hz ; lift z to ℕ using hz; rintro rfl; rw [Ex649u]; split_ifs <;> norm_num <;> positivity
  intro r hr; contrapose! hr;
  by_cases h : r = ⊤; use Example_6_4_9.upperseq (0:ℕ); use (0:ℕ); rw [Ex649u 0]; simp [h]; exact
    compareOfLessAndEq_eq_lt.mp rfl
  obtain ⟨r,rfl⟩ := EReal.real_of_not_top_bot r (by aesop)
  simp at hr; choose n hn using exists_nat_gt (1/r); use Example_6_4_9.upperseq (2*n:ℕ); use (2*n:ℕ);
  constructor; simp; constructor; rfl; rw [Ex649u]; simp;
  rw [inv_lt_comm₀]; rw [← one_div]; linarith; positivity; assumption

lemma Ex649l (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by
  unfold Sequence.lowerseq; apply le_antisymm
  · (have := @Sequence.ge_inf (Example_6_4_9.from ↑n)); simp_rw [ge_iff_le] at this
    split_ifs with h; convert @this (n+1:ℕ) ?_; simp; split_ifs with h1 h2; grind; ring; grind; simp
    convert @this (n:ℕ) ?_; simp [h]; simp
  apply Sequence.inf_ge_lower; intro z hz; simp at hz; simp [hz]; simp [show 0 ≤ z by linarith]
  lift z to ℕ using (by linarith); split_ifs with h1 h2;
  any_goals try apply le_trans (b:=0); simp; positivity; positivity
  replace hz := by simpa using lt_of_le_of_ne hz (by grind)
  (simp; gcongr 1; norm_cast; linarith); simp; gcongr; norm_cast at *

#check EReal.inf_eq_neg_sup

lemma EReal.sup_eq_neg_inf {S : Set EReal}: sSup S = - sInf (-S) := by
  rw [EReal.inf_eq_neg_sup]; simp

example : Example_6_4_9.liminf = 0 := by
  rw [← isLUB_iff_sSup_eq]; constructor <;> simp [lowerBounds, upperBounds]
  · intro r z hz ; lift z to ℕ using hz; rintro rfl; rw [Ex649l]; split_ifs <;> norm_num <;> positivity
  intro r hr; contrapose! hr;
  by_cases h : r = ⊥; use Example_6_4_9.lowerseq (0:ℕ); use (0:ℕ); rw [Ex649l 0]; simp [h]; exact
    compareOfLessAndEq_eq_lt.mp rfl
  obtain ⟨r,rfl⟩ := EReal.real_of_not_top_bot r (by aesop)
  simp at hr; choose n hn using exists_nat_gt (-(1/r)); use Example_6_4_9.lowerseq (2*n:ℕ); use (2*n:ℕ);
  constructor; simp; constructor; rfl; rw [Ex649l]; norm_cast; simp; refine lt_neg_of_lt_neg ?_
  rw [inv_lt_comm₀]; rw [← one_div]; linarith; positivity; linarith

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

lemma Ex6410u (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by
  unfold Sequence.upperseq; rw [sSup_eq_top] ; intro r hr
  by_cases h : r = ⊥; use (Example_6_4_10.from ↑n) (n:ℕ); simp [h]; constructor; use (n:ℤ); simp; constructor; any_goals exact compareOfLessAndEq_eq_lt.mp rfl
  obtain ⟨r,rfl⟩ := EReal.real_of_not_top_bot r (by aesop)
  obtain ⟨m, hm⟩ := exists_nat_gt r; use (Example_6_4_10.from ↑n) (m+n); simp; constructor; use (m+n:ℤ); simp; split_ifs with h1; (norm_cast; rw [Int.toNat_natCast]; push_cast; linarith); grind

example : Example_6_4_10.limsup = ⊤ := by
  unfold Sequence.limsup; rw [sInf_eq_top]; intro r hr; simp at hr;
  obtain ⟨N, hN, rfl⟩ := hr; lift N to ℕ using hN;  rw [Ex6410u N]

lemma Ex6410l (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by
  unfold Sequence.lowerseq Sequence.inf; apply le_antisymm
  · apply csInf_le; use 0; simp [lowerBounds]; intro r z hz; simp [hz]; have : 0 ≤ z := by linarith
    simp [this]; rintro rfl; norm_cast; simp; use n; simp
  apply Sequence.inf_ge_lower; intro z hz; simp at hz; simp [hz]; have : 0 ≤ z := by linarith
  lift z to ℕ using this; simp; rw [← EReal.coe_one]; norm_cast at *; linarith

example : Example_6_4_10.liminf = ⊤ := by
  unfold Sequence.liminf; rw [sSup_eq_top]; intro r hr;
  by_cases h : r = ⊥;
    use Example_6_4_10.lowerseq (0:ℕ); constructor; use (0:ℕ); simp; subst h; rw [Ex6410l 0]; simp; norm_cast
  obtain ⟨r,rfl⟩ := EReal.real_of_not_top_bot r (by aesop)
  obtain ⟨n, hn⟩ := exists_nat_gt r; use Example_6_4_10.lowerseq (n:ℕ); constructor; use (n:ℕ); simp; rw [Ex6410l n];
  rw [← EReal.coe_one]; norm_cast; simp; linarith

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp [limsup, sInf_lt_iff] at h
  obtain ⟨_, ⟨ N, ⟨ hN, rfl ⟩ ⟩, ha ⟩ := h; use N  -- Grab sup_N
  simp [hN, upperseq] at ha ⊢; intro n _  -- Grab a_n
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp [liminf, lt_sSup_iff] at h
  obtain ⟨_, ⟨ N, ⟨ hN, rfl ⟩ ⟩, ha ⟩ := h; use N;
  simp [hN, lowerseq] at ha ⊢
  intro n hn; apply lt_of_lt_of_le ha ?_
  rw [show (a.seq n) = (a.from N).seq n by grind]
  apply (a.from N).ge_inf; grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by apply lt_of_lt_of_le h (sInf_le _); simp; use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  have hx : x > a.lowerseq N := by apply lt_of_le_of_lt (le_sSup _) h; simp; grind
  choose n hn hxn _ using exists_between_gt_inf hx
  grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  apply le_sSup; simp; use a.m; simp; grind


#check EReal.exists_between_lt_sup
#check EReal.exists_between_gt_inf

lemma Sequence.mono_from_sup (a : Sequence) (N M : ℤ) (hN : N ≥ a.m) (hM : M ≥ a.m) (hNM : N ≤ M) :
  (a.from M).sup ≤ (a.from N).sup  := by
  apply Sequence.sup_le_upper; intro z hz; simp at hz; have ⟨hz1, hz2⟩ := hz
  suffices (a.from M).seq z = (a.from N).seq z by rw [this]; apply le_sup; grind
  grind

lemma Sequence.mono_from_inf (a : Sequence) (N M : ℤ) (hN : N ≥ a.m) (hM : M ≥ a.m) (hNM : N ≤ M) :
  (a.from N).inf ≤ (a.from M).inf  := by
  apply inf_ge_lower; intro z hz; simp at hz; have ⟨hz1, hz2⟩ := hz
  suffices (a.from M).seq z = (a.from N).seq z by rw [this]; apply ge_inf; grind
  grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by -- WAY easier approach
  apply le_sInf; intro _ h; simp at h; obtain ⟨N, hN, rfl⟩ := h
  apply sSup_le; intro _ h; simp at h; obtain ⟨M, hM, rfl⟩ := h
  apply le_trans (b := (a (max N M) : EReal))
  apply sInf_le; use max N M; simp_all
  apply le_sSup; use max N M; simp_all


-- In retrospect this old approach is just the same as the one above but like. Flipped around
-- And ugly
/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup' (a:Sequence) : a.liminf ≤ a.limsup := by
  by_contra! hc; unfold liminf at *;
  choose r hr1 hr2 hr3 using EReal.exists_between_lt_sup hc (by use a.lowerseq a.m; use a.m)
  obtain ⟨N, hN, rfl⟩ := hr1
  unfold limsup at hr2;
  choose p hp1 hp2 hp3 using EReal.exists_between_gt_inf hr2 (by use a.upperseq N; use N)
  obtain ⟨M, hM, rfl⟩ := hp1
  unfold lowerseq upperseq at hp2
  let Q := max N M; have hQ : Q ≥ a.m := by unfold Q; simp; grind
  suffices a.from Q Q < a.from Q Q by exact (lt_self_iff_false (_)).mp this
  rw [← EReal.coe_lt_coe_iff]
  calc
    (a.from Q).seq Q ≤ (a.from Q).sup := by apply EReal.mem_le_sup ; simp; use Q; simp [hQ]
    _ ≤ (a.from M).sup := by apply mono_from_sup; grind; grind; simp [Q]
    _ < (a.from N).inf := hp2
    _ ≤ (a.from Q).inf := by apply mono_from_inf; linarith; linarith; simp [Q]
    _ ≤ a.from Q Q := by apply EReal.mem_ge_inf; simp; use Q; simp [hQ]


/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  apply sInf_le; simp; use a.m; simp; grind

lemma Sequence.inf_le_sup (a:Sequence) : a.inf ≤ a.sup :=  le_trans (a.inf_le_liminf) (le_trans a.liminf_le_limsup a.limsup_le_sup)


#check Sequence.sup_ne_bot
#check Sequence.inf_ne_top

lemma EReal.real_of_not_top_bot' (x : EReal) (h1 : x ≠ ⊤) (h2 : x ≠ ⊥) : ∃ r : ℝ, x = r := by
  apply EReal.real_of_not_top_bot; simp [h1, h2]




#check Sequence.lt_liminf_bounds
/-
lt_liminf_bounds gives the sequence of elements greater than c, but those elements aren't bounded away from c.

To bound them away from c, you'd need to have c+e < liminf. But since liminf *could* be infinite, you can't just go halfway
between c and liminf.

Ultimately, we could force this to work, but it requires cleaning up. Instead, we should just grab an inf > c, and use that as
a bound.
-/

#check EReal.exists_between_coe_real -- This will be useful for getting between elems


lemma lt_epsilon {a: ℝ } (h: ∀ e > 0, a < e ) : a ≤ 0 := by
  contrapose! h; use a/2; constructor <;> linarith

lemma le_epsilon {a: ℝ } (h: ∀ e > 0, a ≤ e ) : a ≤ 0 := by
  contrapose! h; use a/2; constructor <;> linarith



-- If we take the contrapose, we get lt_liminf and gt_limsup, which give us what we want (elems outside range)
-- Using these theorems directly let's us skip getting a sup/inf
theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  rw [limit_point_def] at h; constructor
  · contrapose! h; choose d hd1 hd2 using EReal.exists_between_coe_real h -- c < p, so we can find a real between them
    refine ⟨d-c, by simp_all, ?_⟩; peel (lt_liminf_bounds hd2) with N hN n hn this;
    rw [abs_of_pos (by simp_all; grind)]; simp_all
  contrapose! h; choose d hd1 hd2 using EReal.exists_between_coe_real h -- c > p, so we can find a real between them
  refine ⟨c-d, by simp_all, ?_⟩; peel (gt_limsup_bounds hd1) with N hN n hn this;
  rw [abs_of_neg (by simp_all; grind)]; simp_all

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
theorem Sequence.limit_point_between_liminf_limsup' {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  rw [limit_point_def] at h; constructor
  · contrapose! h; -- p is inf. Since a(n) can't go below p, it can't get close to c
    obtain ⟨_,⟨N,_,rfl⟩,hcp,_⟩ := EReal.exists_between_lt_sup h (by use a.lowerseq a.m, a.m) -- c < p
    obtain ⟨p, hp⟩ := EReal.real_of_not_top_bot' ((a.from N).inf) inf_ne_top (ne_bot_of_gt hcp) -- ∈ ℝ
    have hinf n:= hp ▸ (@ge_inf n (a:= a.from N)) -- p ≤ a(n)
    use (p-c)/2; simp_all; use N; simp_all; -- p-c is minimum distance (≤). use (p-c)/2 for (<).
    peel hinf with n hn hinf; rw [abs_of_pos (by grind)]; linarith -- c < p ≤ a(n)
  contrapose! h
  obtain ⟨_,⟨N,_,rfl⟩,hcp,_⟩ := EReal.exists_between_gt_inf h (by use a.upperseq a.m, a.m)
  obtain ⟨p, hp⟩ := EReal.real_of_not_top_bot' ((a.from N).sup) (LT.lt.ne_top hcp) sup_ne_bot
  have hsup n:= hp ▸ (@le_sup n (a:= a.from N)) -- a(n) ≤ p
  use (c-p)/2; simp_all; use N; simp_all;
  peel hsup with n hn hsup; rw [abs_of_neg (by grind)]; linarith -- a(n) ≤ p < c




theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  unfold Sequence.LimitPoint; intro e he N hN;
  choose M hM0 hM using Sequence.gt_limsup_bounds (a:=a) (x:= (L_plus + e/2:ℝ))
    (by rw [h, gt_iff_lt, EReal.coe_lt_coe_iff]; simp; grind)
  choose P hPM hP using Sequence.lt_limsup_bounds (a:=a) (x:= (L_plus - e/2:ℝ)) (N := max N M)
    (by rw [h, EReal.coe_lt_coe_iff]; simp; grind) (by grind)
  specialize hM P (by grind); rw [gt_iff_lt, EReal.coe_lt_coe_iff] at *
  use P; constructor; simp_all; simp [dist];
  split_ifs with h; swap; contrapose! h; simp_all; linarith
  rw [abs_le]; constructor <;> linarith

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  unfold Sequence.LimitPoint; intro e he N hN;
  choose M hM0 hM using Sequence.lt_liminf_bounds (a:=a) (y:= (L_minus - e/2:ℝ))
    (by rw [h, EReal.coe_lt_coe_iff]; simp; grind)
  choose P hPM hP using Sequence.gt_liminf_bounds (a:=a) (x:= (L_minus + e/2:ℝ)) (N := max N M)
    (by rw [h, gt_iff_lt, EReal.coe_lt_coe_iff]; simp; grind) (by grind)
  specialize hM P (by grind); rw [gt_iff_lt, EReal.coe_lt_coe_iff] at *
  use P; constructor; simp_all; simp [dist];
  split_ifs with h; swap; contrapose! h; simp_all; linarith
  rw [abs_le]; constructor <;> linarith

#check Sequence.bounded_of_convergent
#check Sequence.sup_of_bounded

lemma Sequence.limsup_of_bounded {a:Sequence} (h: a.IsBounded) : a.limsup.IsFinite := by
  obtain ⟨s, hs⟩ := Sequence.sup_of_bounded h
  obtain ⟨i, hi⟩ := Sequence.inf_of_bounded h
  have hss := Sequence.limsup_le_sup a
  have hii := le_trans (Sequence.inf_le_liminf a) (Sequence.liminf_le_limsup a)
  rw [← hs, ← hi] at *
  refine CanLift.prf a.limsup ?_; constructor
  · contrapose! hss; rw [hss]; exact EReal.coe_lt_top s
  · contrapose! hii; rw [hii]; exact EReal.bot_lt_coe i

  lemma Sequence.liminf_of_bounded {a:Sequence} (h: a.IsBounded) : a.liminf.IsFinite := by
  obtain ⟨s, hs⟩ := Sequence.sup_of_bounded h
  obtain ⟨i, hi⟩ := Sequence.inf_of_bounded h
  have hii := Sequence.inf_le_liminf a
  have his := le_trans (Sequence.liminf_le_limsup a) (Sequence.limsup_le_sup a)
  rw [← hs, ← hi] at *
  refine CanLift.prf a.liminf ?_; constructor
  · contrapose! his; rw [his]; exact EReal.coe_lt_top s
  · contrapose! hii; rw [hii]; exact EReal.bot_lt_coe i

-- Rather than going halfway between, just grab an arbitrary element between (saves some work)
theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor
  · intro h; have ⟨h1,h2⟩:= limit_point_between_liminf_limsup (limit_point_of_limit h) -- Limpoint is sufficient for one side of equal
    rw [tendsTo_iff] at *
    constructor
    · apply le_antisymm h1; contrapose! h; choose w hw1 hw2 using EReal.exists_between_coe_real h; -- Elem between
      refine ⟨c-w, by simp_all, ?_⟩; intro N -- Will always go below w sometime (liminf below)
      peel gt_liminf_bounds (N := max N a.m) hw1 (by grind) with n hn;
      simp_all; rw [abs_of_neg (by grind)]; simp_all; -- Clean up
    · apply le_antisymm ?_ h2; contrapose! h; choose w hw1 hw2 using EReal.exists_between_coe_real h; -- Elem between
      refine ⟨w-c, by simp_all, ?_⟩; intro N -- Will always go above w sometime (limsup above)
      peel lt_limsup_bounds (N := max N a.m) hw2 (by grind) with n hn;
      simp_all; rw [abs_of_pos (by grind)]; simp_all; -- Clean up
  rintro ⟨h1, h2⟩; rw [tendsTo_iff] at *; intro e he
  choose N hN0 hN using Sequence.gt_limsup_bounds (a:=a) (x:=(c+e/2:ℝ)) -- eventual upper bound
    (by rw [h2,gt_iff_lt, EReal.coe_lt_coe_iff]; linarith)
  choose M hM0 hM using Sequence.lt_liminf_bounds (a:=a) (y:=(c-e/2:ℝ)) -- eventual lower bound
    (by rw [h1, EReal.coe_lt_coe_iff]; linarith)
  use max N M; intro n hn; specialize hN n (by grind); specialize hM n (by grind);
  rw [gt_iff_lt, EReal.coe_lt_coe_iff] at *;
  rw [abs_le]; constructor <;> linarith -- Combined, a(n) is trapped near c

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
theorem Sequence.tendsTo_iff_eq_limsup_liminf' {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor
  · intro h; have ⟨h1,h2⟩:= limit_point_between_liminf_limsup (limit_point_of_limit h) -- Limpoint is sufficient for one side of equal
    have hb:= Sequence.bounded_of_convergent ⟨c, h⟩
    choose s hs using Sequence.limsup_of_bounded hb; choose i hi using Sequence.liminf_of_bounded hb
    rw [tendsTo_iff] at *
    constructor
    · apply le_antisymm h1; contrapose! h; let d := (c - i)/2; use d; -- Go below halfway between
      have h' := h; simp [← hi] at h; constructor; simp_all [d]
      intro N; have hc: a.liminf < (c-d:ℝ) := by rw [← hi,EReal.coe_lt_coe_iff]; unfold d; linarith
      choose n hn0 hn using gt_liminf_bounds (N := max N a.m) hc (by grind); -- Find elem below halfway
      use n; constructor; grind; have hd: d > 0 := by unfold d; simp [h] -- Show that c-a_n beyond dist d
      rw [EReal.coe_lt_coe_iff] at hn; rw [abs_of_neg (by grind)]; linarith
    · apply le_antisymm ?_ h2; contrapose! h; have h' := h; simp [← hs] at h
      let d := (s - c)/2; use d; have hd: d > 0 := by unfold d; simp [h]
      refine ⟨hd, ?_⟩; intro N
      have hc : (c + d:ℝ) < a.limsup := by rw [← hs, EReal.coe_lt_coe_iff]; unfold d; linarith
      choose n hn0 hn using lt_limsup_bounds (N := max N a.m) hc (by grind);
      use n; constructor; grind
      rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hn; rw [abs_of_pos (by grind)]; linarith
  rintro ⟨h1, h2⟩; rw [tendsTo_iff] at *; intro e he
  choose N hN0 hN using Sequence.gt_limsup_bounds (a:=a) (x:=(c+e/2:ℝ)) -- eventual upper bound
    (by rw [h2,gt_iff_lt, EReal.coe_lt_coe_iff]; linarith)
  choose M hM0 hM using Sequence.lt_liminf_bounds (a:=a) (y:=(c-e/2:ℝ)) -- eventual lower bound
    (by rw [h1, EReal.coe_lt_coe_iff]; linarith)
  use max N M; intro n hn; specialize hN n (by grind); specialize hM n (by grind);
  rw [gt_iff_lt, EReal.coe_lt_coe_iff] at *;
  rw [abs_le]; constructor <;> linarith -- Combined, a(n) is trapped near c





#check Sequence.exists_between_lt_sup

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
    contrapose! hab;  choose n hn0 hn1 _ using Sequence.exists_between_lt_sup hab
    use n; simp [hn0]; rw [← EReal.coe_lt_coe_iff];
    exact lt_of_le_of_lt (le_sup (hm ▸ hn0)) hn1


/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by
    contrapose! hab;  choose n hn0 hn1 _ using Sequence.exists_between_gt_inf hab
    use n; simp [hm ▸ hn0]; rw [← EReal.coe_lt_coe_iff];
    apply lt_of_lt_of_le hn1 (ge_inf (hm ▸ hn0))

#check Sequence.exists_between_gt_inf




/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
  contrapose! hab;
  obtain ⟨x, hx1, hx2, hx3⟩ := EReal.exists_between_gt_inf hab (by use b.upperseq a.m; use a.m; simp_all)
  obtain ⟨N, hN0, rfl⟩ := hx1
  choose n hn0 hn using Sequence.lt_limsup_bounds hx2 (N := N) (by simp_all)
  use n; constructor; linarith
  rw [← EReal.coe_lt_coe_iff]; apply lt_of_le_of_lt ?_ hn; unfold upperseq Sequence.sup
  apply EReal.mem_le_sup; use n; simp_all


-- We can use ≤ without having to contrapose to < because sup_mono uses ≤
theorem Sequence.limsup_mono' {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
  apply le_csInf (by use b.upperseq a.m; use a.m; simp_all); intro z hz; obtain ⟨N,hN, rfl⟩ := hz
  apply le_trans (b:= a.upperseq N) (sInf_le (by use N; simp_all))
  unfold upperseq; apply sup_mono (by grind) (by grind)


/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by
  apply csSup_le (by use a.lowerseq a.m; use a.m); intro z hz; obtain ⟨N,hN, rfl⟩ := hz
  apply le_trans (b:= b.lowerseq N) ?_ (le_sSup (by use N; simp_all))
  unfold lowerseq; apply inf_mono (by grind) (by grind)

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (habc: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hc: c.TendsTo L) :
    b.TendsTo L := by
  rw [tendsTo_iff] at *; intro e he; choose N ha using ha e he; choose M hc using hc e he; use max (max N M) a.m
  intro n hn; simp_rw [abs_le] at * -- upper bound a + e is at least as good as b + e, and same for c - e
  have ⟨ha1, ha2⟩ := ha n (by grind); have ⟨hc1, hc2⟩ := hc n (by grind); have ⟨hab, hbc⟩ := habc n (by grind)
  constructor <;> linarith

/-- Example 6.4.15 -/
lemma ex6_4_15 : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  convert Sequence.tendsTo_smul 2 (Sequence.lim_eq.mpr Sequence.lim_harmonic)
  rw [Sequence.smul_coe]; grind; simp

/-- Example 6.4.15 -/
lemma ex6_4_15' : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  convert Sequence.tendsTo_smul (-2) (Sequence.lim_eq.mpr Sequence.lim_harmonic)
  rw [Sequence.smul_coe]; grind; simp

lemma neg_one_pow_lower (n: ℕ) : (-1:ℝ) ≤ (-1) ^ n := by
  rcases (neg_one_pow_eq_or ℝ n) with h | h <;> rw [h]; simp


lemma neg_one_pow_upper (n: ℕ) : (-1:ℝ) ^ n ≤ 1 := by
  rcases (neg_one_pow_eq_or ℝ n) with h | h <;> rw [h]; simp

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  apply Sequence.lim_of_between (by simp) ?_ ex6_4_15' ex6_4_15
  intro n hn; lift n to ℕ using hn; constructor
  · apply le_trans ?_ (le_add_of_nonneg_right (by positivity));
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    apply le_trans (by simp) (neg_one_pow_lower n)
  simp only [ge_iff_le, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]
  have : (n:ℝ) + 1 > 0 := by positivity
  rw [sq, le_div_iff₀ this, add_mul, show (2:ℝ) = 1 + 1 by norm_num]; apply add_le_add;
  · field_simp; exact neg_one_pow_upper n
  · field_simp; rw [(div_le_one this)]; aesop

theorem Sequence.tendsTo_const (r : ℝ ):
  (fun (_:ℕ) => r : Sequence).TendsTo r := by
  rw [Sequence.lim_eq]; exact lim_const r

theorem Sequence.tendsTo_harmonic : ((fun (n:ℕ) ↦ 1/(n+1:ℝ)):Sequence).TendsTo 0 := by
  rw [Sequence.lim_eq]; convert lim_harmonic using 4 <;> simp

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  apply Sequence.lim_of_between (by simp) ?_ (Sequence.tendsTo_const 0) (Sequence.tendsTo_harmonic)
  intro n hn; lift n to ℕ using hn; constructor; simp
  simp; refine inv_anti₀ (by positivity) ?_;
  induction' n with n ih; norm_num
  · apply le_trans (b := (2*(n+1):ℝ)) (by rw [two_mul]; field_simp) ?_
    rw [pow_succ' 2 n]; simp_all

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  (repeat rw [tendsTo_iff]); peel with e he N n hN; congr! 1; unfold abs; simp

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←EReal.coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply EReal.coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←EReal.coe_neg]
  use a.liminf.toReal; symm; apply EReal.coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←EReal.coe_neg]

/-It seems I already created this helper lemma up above, as two lemmas?
limsup_of_bounded and liminf_of_bounded.-/

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  · specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  use (·), (·+1); constructor
  · intro n; linarith
  apply not_lt_of_ge; apply ge_of_eq; apply Eq.trans (b := ⊤) -- Both sups are ⊤
  swap; symm;
  all_goals ( rw [sSup_eq_top]; intro x hx; -- Handle x = ⊥ case
              by_cases hbot : x = ⊥; subst hbot; use 1; constructor
              any_goals exact compareOfLessAndEq_eq_lt.mp rfl;)
  (on_goal 1 => use 0); (on_goal 3 => use 1); any_goals simp -- Handle offset, close case

  all_goals ( obtain ⟨r, rfl⟩ := EReal.real_of_not_top_bot' x (LT.lt.ne_top hx) hbot -- x is a real
              choose n hn using exists_nat_gt r)
  (on_goal 1 => use (n+1:ℝ)); (on_goal 2 => use (n:ℝ)) -- Handle offset
  all_goals (constructor; use n; have: 0 ≤ (n :ℤ) := by linarith -- Close case
             simp_all; rw [EReal.coe_lt_coe_iff]; linarith)


/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  apply isFalse -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  push_neg; use ((-1 : ℕ → ℝ ) : Sequence); use -1; left; repeat rw  [tendsTo_iff];
  constructor; intro e he; use 0; intro n hn; simp [hn]; order
  push_neg; use 1; simp; intro n; use max 0 n; simp; norm_num

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by
  unfold ExtendedLimitPoint BddAbove BddAboveBy BddBelow BddBelowBy limsup; push_neg
  split_ifs with htop hbot
  · rw [sInf_eq_top] at htop; specialize htop (a.upperseq a.m) (by simp; grind) -- sup_a.m = ⊤
    rw [sSup_eq_top] at htop; intro r; obtain ⟨an, ⟨z, hz, rfl⟩, h⟩ := htop r (by simp) -- Find a_z > r
    use z; simp_all
  · rw [sInf_eq_bot] at hbot; intro r; obtain ⟨sup, ⟨z, hz, rfl⟩, h⟩ := hbot r (by simp); -- Find sup_z < r
    use z; simp [hz]; rw [← EReal.coe_lt_coe_iff]; apply lt_of_le_of_lt ?_ h
    apply le_sSup; simp; use z; grind -- -- sup_z ≤ a_z < r
  obtain ⟨L, hL⟩ := EReal.real_of_not_top_bot' a.limsup htop hbot; unfold limsup at hL
  rw [hL]; simp; exact limit_point_of_limsup hL -- Else, already solved

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by
  unfold ExtendedLimitPoint BddAbove BddAboveBy BddBelow BddBelowBy liminf; push_neg
  split_ifs with htop hbot
  · rw [sSup_eq_top] at htop; intro r; obtain ⟨sup, ⟨z, hz, rfl⟩, h⟩ := htop r (by simp); -- Find inf_z > r
    use z; simp [hz]; rw [← EReal.coe_lt_coe_iff]; apply lt_of_lt_of_le h ?_;
    apply sInf_le; simp; use z; grind -- r < inf_z ≤ a_z
  · rw [sSup_eq_bot] at hbot; specialize hbot (a.lowerseq a.m) (by simp; grind) -- inf_a.m = ⊥
    rw [sInf_eq_bot] at hbot; intro r; obtain ⟨an, ⟨z, hz, rfl⟩, h⟩ := hbot r (by simp) -- Find a_z < r
    use z; simp_all
  obtain ⟨L, hL⟩ := EReal.real_of_not_top_bot' a.liminf htop hbot; unfold liminf at hL
  rw [hL]; simp; exact limit_point_of_liminf hL


abbrev Sequence.start_subset (a:Sequence) (z: ℤ) : Set ℝ := {x | ∃ n, a.m ≤ n ∧ n < z ∧ x = a n}

lemma Sequence.start_subset_bddAbove (a : Sequence) (z : ℤ) :
    ∃ r, ∀ x ∈ start_subset a z, x ≤ r := by
  by_cases h : z < a.m
  · use 0; unfold start_subset; rintro x ⟨n, hn1, hn2, rfl⟩; linarith
  lift (z - a.m) to ℕ using (by omega) with t ht; simp_rw [show z = a.m + t by omega]; clear ht
  induction' t with t ih -- Induct over the length of the start subset
  · use 0; intro x hx; obtain ⟨n, hn1, hn2, rfl⟩ := hx; simp at hn2; exfalso; linarith
  obtain ⟨r, h⟩ := ih; use max r (a (a.m + t)); -- Either in ih or the last element
  intro x hx; obtain ⟨n, hn1, hn2, rfl⟩ := hx; simp at hn2
  by_cases hle: n = a.m + t; subst hle; aesop
  specialize h (a.seq n) (by use n; simp; constructor <;> omega)
  aesop


lemma Sequence.bddabove_subseq_bddabove_seq (a:Sequence) (z: ℤ) (h: BddAbove (a.from z))  : a.BddAbove := by
  choose M hM using h; choose N hN using Sequence.start_subset_bddAbove a z
  use max M N; intro n hn; by_cases hle: n < z
  · specialize hN (a.seq n) (by use n); aesop
  specialize hM n (by simp; constructor <;> omega); aesop


theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by
  unfold ExtendedLimitPoint at h;
  induction' L using EReal.rec with r
  · order
  · apply (limit_point_between_liminf_limsup' h).2
  simp only [↓reduceIte] at h -- Cleanup into ¬ BddAbove a → limsup = ⊤
  rw [top_le_iff,sInf_eq_top]; rintro _ ⟨z, hz, rfl⟩; rw [sSup_eq_top] -- sup_i = ⊤ (sequence unbounded above)
  intro e he; by_cases hbot: e = ⊥ -- ⊥ case solved, so we can assume e is real
  · subst hbot; use a.from z z; constructor; use z; grind; simp
  lift e to ℝ using (by constructor <;> order);
  apply (bddabove_subseq_bddabove_seq a z).mt at h -- all sup_i terms are unbounded above
  unfold BddAbove BddAboveBy at h; push_neg at h --
  choose n hn1 hn2 using h e; use (a.from z).seq n; constructor; use n; aesop

lemma Sequence.neg_ExtendedLimitPoint {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): (-a).ExtendedLimitPoint (-L) := by
  unfold ExtendedLimitPoint at *; split_ifs with htop hbot <;> simp at htop
  · simp only [htop, bot_ne_top, ↓reduceIte] at h; contrapose! h; exact
    (neg_BddAbove a).mpr h
  · simp at hbot; simp only [hbot, ↓reduceIte] at h; contrapose! h; exact
    (neg_BddBelow a).mpr h
  simp at hbot; simp only [hbot, htop, ↓reduceIte] at h;
  peel h with e he n hn z hz h -- Third case just requires some manipulation
  simp_all [dist, show (-a).m = a.m by aesop];
  convert h using 1; rw [abs_eq_abs]; right; linarith

lemma Sequence.neg_lowerseq {a:Sequence} : -(a).lowerseq = (-a).upperseq := by
  unfold lowerseq upperseq; ext i; simp; unfold inf sup;
  rw [EReal.sup_eq_neg_inf]; congr; ext j; simp [show (-a).m = a.m by aesop];
  peel with n hn; rw [neg_eq_iff_eq_neg]; constructor <;> intro h <;> subst h <;> aesop

lemma Sequence.neg_liminf {a:Sequence} : - a.liminf = (-a).limsup  := by
  unfold liminf limsup; rw [EReal.sup_eq_neg_inf]; simp [show (-a).m = a.m by aesop]; congr! 1;
  ext i; simp; rw [← neg_lowerseq]; simp [neg_eq_iff_eq_neg]

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by
  apply neg_ExtendedLimitPoint at h; rw [ge_iff_le, ← EReal.neg_le_neg_iff]
  rw [neg_liminf]; exact extended_limit_point_le_limsup h

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by
  let f : ℕ → ℝ := fun m ↦ if Even m then m*(-1)^(m/2) else 0; -- Even terms alternate between pos and neg, based on n/2 polarity
  use f; intro L; constructor <;> intro h -- Minimize dist: 1. dist btwn abs 2. pick min from odd (|r|) and even (|n|-|r|) terms
  · contrapose! h; have ⟨h1,h2,h3⟩:=h; lift L to ℝ using ⟨h3,h1⟩; simp at h2; unfold ExtendedLimitPoint; simp [h1,h3]
    choose n hn using exists_nat_gt (|L|); use min (|L|/2) ((|(n:ℝ)|-|L|)/2); refine ⟨lt_min (by simp [h2]) (by simp [hn]), ?_⟩
    use n; refine ⟨by grind, ?_⟩; intro z hz hnz; lift z to ℕ using hz; simp_all
    by_cases h : Even z <;> [right; left] <;> simp [dist, f, h] -- As mentioned above: use abs distance
    · apply lt_of_lt_of_le ?_ (abs_abs_sub_abs_le _ _); simp [abs_mul];
      have hz: 0 < (z:ℝ) - |L| := by simp_all; apply lt_of_lt_of_le hn (by simp_all) -- Slight annoyance
      nth_rw 2 [abs_of_pos (by grind)]; apply lt_of_le_of_lt ?_ (half_lt_self hz); gcongr
    exact h2 -- L is always at least L/2 away from 0
  rcases h with (rfl | rfl | rfl) -- n>r doesn't mean -n<r. We choose n further from 0 than r: |r|<n. So, -n < |r| ≤ r .
  · unfold ExtendedLimitPoint; simp; intro r; choose n hn using exists_nat_gt (|r|); use 2*(2*n+1); simp [f]; use (by omega)
    rw [if_pos (by omega),if_pos ⟨2*n+1, by omega⟩, Odd.neg_one_pow ⟨n, by omega⟩]; simp; -- Choose n/2 odd: neg term below r
    apply lt_of_lt_of_le ?_ (neg_abs_le r); simp; apply lt_trans hn; simp; omega -- Choosing odd required bigger m than n.
  · intro e he z hz; use 2*z+1; refine ⟨by grind, ?_⟩; simp [f]; -- Odd term, so we get exactly 0
    rw [if_pos (by grind), if_pos (by grind), if_neg (by grind)]; simp; linarith -- Just need to handle a bunch of side conds
  unfold ExtendedLimitPoint; simp; intro r; choose n hn using exists_nat_gt r; use 2*(2*n); simp [f] -- Choose n/2 even: pos above r
  rw [if_pos ⟨2*n, by omega⟩, Even.neg_one_pow ⟨n, by omega⟩]; apply lt_of_lt_of_le hn; simp; omega -- Choose even required bigger m than n.

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by
  unfold LimitPoint at *; intro e he N hN;
  obtain ⟨n, hn, hbc⟩ := hbc (e/3) (by aesop) (max N b.m) (by aesop);
  obtain ⟨m, hm, hab⟩ := hab n (by aesop) (e/3) (by aesop) (max N a.m) (by aesop);
  simp at *; obtain ⟨hn1, hn2⟩ := hn; obtain ⟨hm1, hm2⟩ := hm;
  use m, (by simp_all); simp [hn1,hn2, hm1,hm2] at *;
  apply le_trans (dist_triangle _ ( b.seq n) _) (by linarith)


end Chapter6
