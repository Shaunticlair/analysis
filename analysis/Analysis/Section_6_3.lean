import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/
set_option linter.unusedVariables false

namespace Chapter6

lemma Sequence.neg_start (a:Sequence) : (-a).m = a.m := by simp [neg]

abbrev Sequence.toSet (a:Sequence) : Set EReal := { x | ∃ n ≥ a.m, x = a n }

lemma Sequence.nonempty (a: Sequence): (Sequence.toSet a).Nonempty := by
  use a a.m; simp; use a.m

--Add coercion
instance : Coe (Sequence) (Set EReal) := ⟨Sequence.toSet⟩

lemma Sequence.neg_toSet (a:Sequence) : (-a).toSet = - a.toSet := by
    ext i; simp [Sequence.toSet, neg_start ];
    constructor <;> rintro ⟨n, hn, h⟩ <;> use n <;> simp [hn];
    rw [h]; simp; rw [← h]; simp

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup a

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf a

lemma Sequence.neg_sup_inf (a:Sequence) : -(-a).sup = a.inf := by
    simp [Sequence.sup, Sequence.inf, neg_toSet, EReal.inf_eq_neg_sup]

lemma Sequence.neg_inf_sup (a:Sequence) : -(-a).inf = a.sup := by
    simp [Sequence.inf, Sequence.sup, neg_toSet, EReal.inf_eq_neg_sup]


-- Mathlib definitions for sup (related to `EReal.mem_le_sup` and `EReal.sup_le_upper`)
#check le_csSup
#check csSup_le
-- I could use our chapter-built ones, but honestly it's preferable to get used to mathlib.

lemma neg_one_pow (n:ℕ) : (-1:ℝ)^n = 1 ∨ (-1:ℝ)^n = -1 := by
  exact neg_one_pow_eq_or ℝ n

/-- Example 6.3.3 -/
lemma ex_6_3_3a : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
    unfold Sequence.sup; apply le_antisymm
    ·   apply csSup_le (by use -1; simp; use 0; simp)
        intro x hx; simp at hx; choose n hn hx using hx; simp [hn] at hx
        rcases neg_one_pow_eq_or EReal (n.toNat + 1) with (h | h) <;> rw [h] at hx <;> subst hx
        exact EReal.refl 1; apply EReal.coe_le_coe_iff.mpr; linarith
    apply le_csSup ?_ (by simp; use 1; simp)
    use 1; simp [upperBounds]; rintro x z hz rfl; simp [hz];
    rcases neg_one_pow_eq_or EReal (z.toNat + 1) with (h | h) <;> rw [h]
    apply EReal.coe_le_coe_iff.mpr; linarith

example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
    unfold Sequence.inf; rw [EReal.inf_eq_neg_sup]; simp only [neg_inj]
    convert ex_6_3_3a using 1; congr;
    ext i; simp
    constructor <;> rintro ⟨n, hn, h⟩ <;> simp [hn] at h <;> use n+1 <;> refine ⟨by linarith, ?_⟩
    <;> split_ifs with hn <;> try linarith
    all_goals (replace h := congr_arg (fun x ↦ (-1)^1*x) h; simp only at h;
               (conv at h => lhs; simp); rw [h]; push_cast; rw [← pow_add]; congr 1; omega)



/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
    unfold Sequence.sup; apply le_antisymm
    apply csSup_le (by use 1; simp; use 0; simp)
    intro x hx; simp at hx; choose n hn hx using hx; simp [hn] at hx; subst x
    swap
    apply le_csSup ?_ (by simp; use 0; simp)
    use 1; simp [upperBounds]; rintro x n hn rfl; simp [hn];
    all_goals (apply EReal.coe_le_coe_iff.mpr; field_simp; rw [div_le_one₀]; simp;
                lift n to ℕ using hn; linarith)

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
    rw [← isGLB_iff_sInf_eq]
    constructor <;> simp [lowerBounds, upperBounds]
    ·   intro x z hz hx; subst hx; simp [hz]; positivity
    intro x h1; contrapose! h1;
    rcases EReal.def x with ⟨r, rfl⟩ | rfl | rfl
    ·   choose n hn using exists_nat_gt (1/r); use 1/(n+1); use n; simp
        refine ⟨by norm_cast, ?_⟩; norm_cast; norm_cast at h1
        rw [show ((n+1:ℕ):EReal) = ((n+1:ℝ):EReal) from by push_cast; ring_nf,← EReal.coe_inv]
        rw [EReal.coe_lt_coe_iff]; rw [← one_div];rw [div_lt_iff₀] at *; ring_nf at *
        all_goals linarith
    · use 1, 0; simp; exact EReal.lt_top 1
    exfalso; simp at h1




/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
    unfold Sequence.sup; rw [sSup_eq_top] -- Unboundedness statement
    intro x hx; rcases EReal.def x with ⟨r, rfl⟩ | rfl | rfl
    ·   choose n hn using exists_nat_gt r;
        use n+1; simp; refine ⟨?_, by exact_mod_cast (by linarith: r < n+1)⟩
        use n; simp
    simp at hx;
    use 1; simp; refine ⟨by use 0; simp, by rw [EReal.lt_iff]; tauto ⟩


/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
    unfold Sequence.inf; apply le_antisymm
    ·   apply csInf_le ?_ (by simp; use 0; simp)
        use 1; simp [lowerBounds]; rintro x n hn rfl; simp [hn];
        lift n to ℕ using hn; simp; apply EReal.coe_le_coe_iff.mpr; simp
    apply le_csInf (by use 1; simp; use 0; simp)
    intro x hx; simp at hx; choose n hn hx using hx; simp [hn] at hx; subst x;
    lift n to ℕ using hn; simp; apply EReal.coe_le_coe_iff.mpr; simp


abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

lemma Sequence.neg_BddAboveBy (M: ℝ) (a:Sequence) : a.BddAboveBy M ↔ (-a).BddBelowBy (-M) := by
    simp [BddAboveBy, BddBelowBy, neg]

lemma Sequence.neg_BddBelowBy (M: ℝ) (a:Sequence) : a.BddBelowBy M ↔ (-a).BddAboveBy (-M) := by
    simp [BddAboveBy, BddBelowBy, neg]

lemma Sequence.neg_BddBelow (a:Sequence) : a.BddAbove ↔ (-a).BddBelow := by
    constructor <;> rintro ⟨M, hM⟩ <;> use -M; exact (neg_BddAboveBy M a).mp hM
    rw [show a = -(-a) from by simp [neg]]; exact (neg_BddBelowBy M (-a)).mp hM

lemma Sequence.neg_BddAbove (a:Sequence) : a.BddBelow ↔ (-a).BddAbove := by
    constructor <;> rintro ⟨M, hM⟩ <;> use -M; exact (neg_BddBelowBy M a).mp hM
    rw [show a = -(-a) from by simp [neg]]; exact (neg_BddAboveBy M (-a)).mp hM

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
    constructor
    ·   rintro ⟨M, hM0, hM⟩; constructor;
        · use M; intro x hx; exact le_of_max_le_left (hM x)
        use -M; intro x hx; simp; exact neg_le_of_abs_le (hM x)
    rintro ⟨⟨M,hM⟩, ⟨N,hN⟩⟩
    use max (max M (-N)) 0; simp; intro x;
    by_cases hx: x < a.m; simp [a.vanish _ hx]; push_neg at hx
    rcases lt_trichotomy (a.seq x) 0 with h | h | h
    ·   simp [abs_of_neg h]; left; right; apply hN _ hx
    ·   rw [h]; simp
    simp [abs_of_pos h]; left; left; apply hM _ hx

lemma Sequence.bounded_iff_neg_bounded (a:Sequence) :  a.IsBounded ↔ (-a).IsBounded:= by
    simp [Sequence.bounded_iff]; rw [neg_BddBelow]; nth_rw 2 [neg_BddAbove]
    tauto

lemma Sequence.sup_not_top_of_bounded_above {a:Sequence} (h: a.BddAbove) : a.sup ≠ ⊤ := by
    choose M hM using h; simp [sSup_eq_top]; use M; simp;
    rintro x z hz rfl; simp; exact hM z hz

lemma Sequence.sup_not_bot_of_bounded_below {a:Sequence} (h: a.BddBelow) : a.sup ≠ ⊥ := by
    simp; use a (a.m); use a.m; simp;

lemma Sequence.sup_not_top_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup ≠ ⊤ := by
    apply Sequence.sup_not_top_of_bounded_above; simp [Sequence.bounded_iff] at h; tauto

lemma Sequence.sup_not_bot_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup ≠ ⊥ := by
    apply Sequence.sup_not_bot_of_bounded_below; simp [Sequence.bounded_iff] at h; tauto

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
    choose M hM0 hM using h; refine CanLift.prf a.sup ?_; constructor
    apply Sequence.sup_not_top_of_bounded ⟨M, hM0, hM⟩
    apply Sequence.sup_not_bot_of_bounded ⟨M, hM0, hM⟩

lemma EReal.isFinite_iff_neg_isFinite (x:EReal) : x.IsFinite ↔ (-x).IsFinite := by
    constructor <;> rintro ⟨r, hr⟩ <;> use -r <;> simp_all

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
    rw [bounded_iff_neg_bounded] at h; apply sup_of_bounded at h
    rw [EReal.isFinite_iff_neg_isFinite] at h
    convert h using 1; exact Eq.symm (neg_sup_inf a)

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by
    by_cases hsup: a.sup = ⊤; simp [hsup];
    simp [sSup_eq_top] at hsup; choose N hN1 hN2 using hsup
    unfold Sequence.sup; apply le_csSup ?_ (by use n)
    ·   use N; simp [upperBounds]; rintro x z hz rfl;
        apply hN2; apply hz; rfl

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) :
  a.sup ≤ M := by
    unfold Sequence.sup; apply csSup_le (Sequence.nonempty a)
    simp; grind


/-
This is weird because the second conclusion is a given

But that just changes the logical structure a bit (instead of a z ≤ y, we get
y < ↑(a.seq z) → a.sup < ↑(a.seq z))
Which reduces to y < ↑(a.seq z) → False: same thing.
-/

theorem EReal.exists_between_lt_sup {s : Set EReal} {y:EReal} (h: y < sSup s) (hs: s.Nonempty) :
  ∃ z ∈ s, y < z ∧ z ≤ sSup s := by
  contrapose! h; apply csSup_le hs; rintro p hp; specialize h p hp
  by_contra! hy; specialize h hy; contrapose! h; exact EReal.mem_le_sup s hp

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup ) :
  ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
  unfold Sequence.sup at *; choose r hr1 hr2 hr3 using EReal.exists_between_lt_sup h (Sequence.nonempty a);
  obtain ⟨n, hn1, rfl⟩ := hr1; use n

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by
    rw [← neg_sup_inf]; rw [← neg_start] at hn; simp [EReal.neg_le]; exact le_sup hn

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
    unfold Sequence.inf; apply le_csInf (Sequence.nonempty a) ?_
    simp; grind

theorem EReal.exists_between_gt_inf {s : Set EReal} {y:EReal} (h: y > sInf s) (hs: s.Nonempty) :
  ∃ z ∈ s, y > z ∧ z ≥ sInf s := by
  contrapose! h; apply le_csInf hs; rintro p hp; specialize h p hp
  by_contra! hy; specialize h hy; contrapose! h; exact EReal.mem_ge_inf s hp

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
  ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
    contrapose! h; apply le_csInf (Sequence.nonempty a); simp at *;
    rintro x z hz rfl; specialize h z hz; by_contra hy; simp at hy; specialize h hy
    contrapose! h; apply ge_inf hz


lemma EReal.real_of_not_top_bot (x:EReal) (h: x ≠ ⊤ ∧ x ≠ ⊥) : ∃ r:ℝ, x = r := by
    rcases EReal.def x with ⟨r, rfl⟩ | rfl | rfl
    · use r;
    all_goals tauto

lemma Sequence.sup_ne_bot {a:Sequence} : a.sup ≠ ⊥ := by
    simp; use a (a.m); simp; use a.m

lemma Sequence.inf_ne_top {a:Sequence} : a.inf ≠ ⊤ := by
    simp; use a (a.m); simp; use a.m

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

lemma Sequence.neg_isMonotone (a:Sequence) : (-a).IsMonotone ↔ a.IsAntitone := by
    simp [Sequence.IsMonotone, Sequence.IsAntitone, neg_start]

lemma Sequence.neg_isAntitone (a:Sequence) : (-a).IsAntitone ↔ a.IsMonotone := by
    simp [Sequence.IsMonotone, Sequence.IsAntitone, neg_start]

lemma Sequence.real_sup {a:Sequence} (h: a.BddAbove) : ∃ r:ℝ, a.sup = r := by
    apply EReal.real_of_not_top_bot; constructor
    apply Sequence.sup_not_top_of_bounded_above h
    apply Sequence.sup_ne_bot

lemma Sequence.mono_if' {a: Sequence} (ha: a.IsMonotone) {n m:ℤ} (hn : n ≥ a.m)(hnm: m ≥ n) : a m ≥ a n := by
    have: ∃ (i:ℕ), m = n + i := by use (m - n).toNat; simp [hnm]
    obtain ⟨i, hi⟩ := this
    induction' i with i ih generalizing m n
    · simp_all
    simp; subst hi
    specialize ih hn (m:=n+i) (by omega) (by omega)
    apply le_trans ih; specialize ha (n+i) (by omega); simp_all
    convert ha using 2; ring


lemma Sequence.converge_sup_of_monotone {a:Sequence} (hmono: a.IsMonotone) (hbound: a.BddAbove) :
    a.TendsTo ((real_sup hbound).choose) := by
    have hr':= (real_sup hbound).choose_spec; set r := (real_sup hbound).choose
    rw [tendsTo_iff]; intro e he
    choose n hn hr hsup using exists_between_lt_sup (by rw [hr']; norm_cast; linarith: r-e < a.sup)
    use n; intro m hm; rw [abs_of_nonpos ?_];
    norm_cast at hr; simp at *
    linarith [mono_if' hmono hn hm]
    ·   simp; exact_mod_cast (hr' ▸ le_sup (le_trans hn hm))

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
  a.Convergent := ⟨(real_sup hbound).choose, converge_sup_of_monotone hmono hbound⟩

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    lim a = a.sup := by
    rw [(real_sup hbound).choose_spec]; simp
    apply (lim_eq.1 (converge_sup_of_monotone hmono hbound)).2

lemma Sequence.neg_convergent {a:Sequence} : (-a).Convergent ↔ a.Convergent := by
    constructor <;> intro h <;> apply lim_neg at h <;> convert h.1; simp [neg]


theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by
    rw [neg_BddAbove] at hbound; rw [← neg_isMonotone] at hmono; rw [← neg_convergent];
    apply Sequence.convergent_of_monotone hbound hmono

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
    rw [← neg_isMonotone] at hmono; rw [neg_BddAbove] at hbound; rw [← neg_sup_inf]
    rw [← Sequence.lim_of_monotone hbound hmono ];
    have hc:= Sequence.convergent_of_monotone hbound hmono
    norm_cast; rw [← (lim_neg hc).2]; congr; exact Eq.symm (neg_neg a)

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by
    refine ⟨bounded_of_convergent, ?_⟩; intro h; rw [Sequence.bounded_iff] at h;
    refine convergent_of_monotone h.1 ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by
    refine ⟨bounded_of_convergent, ?_⟩; intro h; rw [Sequence.bounded_iff] at h;
    refine convergent_of_antitone h.2 ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-
This seems like more Real API stuff so I'm gonna skip.
-/

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).BddAboveBy 4 := by sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

#check Sequence.lim_smul

/-- Proposition 6.3.10-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := by
    intro z hz; unfold a at *; simp_all; have hz1 : 0 ≤ z + 1 := by linarith
    simp [hz1, ← zpow_natCast, hz];
    rw [← mul_lt_mul_right (zpow_pos hpos z)] at hbound
    apply le_of_lt; convert hbound; rw [zpow_add_one₀ (ne_of_gt hpos)]; ring; ring
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by
    suffices ((fun n ↦ x^(n+1):Sequence)).TendsTo L from ?_ -- Directly use TendsTo def, offset of one term
    · rw [Sequence.lim_eq] at this; convert this.2
    apply Sequence.lim_def at hconv; rw [Sequence.tendsTo_iff] at *;
    peel hconv with e he hconv; choose N hconv using hconv; use max N 0
    intro n hn; simp at hn; convert hconv (n+1) (by linarith) using 3
    simp [a, hn, (by linarith: n+1 ≥ 0)];  congr; omega
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by
    intro h; have := (lim_of_exp (x := 1/x) (by positivity) (by rw [div_lt_one (by linarith)]; exact hbound))
    have hlim:= ( Sequence.lim_mul h this.1 ).2
    rw [this.2] at hlim;
    conv at hlim => lhs; arg 1; rw [Sequence.mul_coe]; simp; arg 1; intro i; rw [mul_inv_cancel₀ (by positivity)];
    simp only [mul_zero, Sequence.lim_const] at hlim; norm_num at hlim
end Chapter6
