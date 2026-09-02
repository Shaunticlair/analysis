import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.Analysis.PSeries

/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))


theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  unfold Series.example_7_2_4;
  obtain ⟨m, rfl⟩ : ∃ m:ℕ, N = m + 1 := ⟨(N-1).toNat, by grind⟩
  induction' m with m ih
  · simp [Series.partial]; norm_num
  rw [Series.partial_succ _ (by linarith)]
  push_cast at *; rw [ih (by linarith)]
  rw [dif_pos (by linarith)];
  ring_nf; rw [sub_eq_add_neg, add_assoc]; congr
  -- The lesson to learn from this: exponents cannot be simplified on their own, at
  -- least with all of these coercions.
  -- So, you have to explicitly extract a constant and then use `zpow_add₀` to pull down.
  rw [show (-1-(m:ℤ)) = 1 + (-2-(m:ℤ)) by ring]
  rw [zpow_add₀ (by norm_num)]
  ring

lemma n_le_pow_n (n:ℕ) : n ≤ (2:ℝ)^n := by
  induction' n with n ih
  · norm_num
  rw [pow_succ'];
  simp; rw [show (2:ℝ)*2^n = 2^n+2^n by ring]
  gcongr; apply one_le_pow₀; norm_num

register_hint omega

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by
  unfold convergesTo
  rw [Metric.tendsto_atTop]; intro e he;
  choose N hN using exists_nat_gt (1/e);
  use N+1; intro n hn;
  rw [Series.example_7_2_4a (by simp_all; omega )]
  simp [dist]
  rw [abs_of_pos (by positivity)]
  simp at hn;
  lift n to ℕ using (by omega)
  calc
  _ ≤ (n:ℝ)⁻¹ := by rw [inv_le_inv₀ (by positivity) (by simp_all; linarith)]; apply n_le_pow_n
  _ ≤ (N:ℝ)⁻¹ := by gcongr; linarith [one_div_pos.mpr he]; omega
  _ < _ := by simp_all; exact inv_lt_of_inv_lt₀ he hN

theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := sum_of_converges Series.example_7_2_4b

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  unfold Series.example_7_2_4';
  obtain ⟨m, rfl⟩ : ∃ m:ℕ, N = m + 1 := ⟨(N-1).toNat, by grind⟩
  induction' m with m ih
  · simp [Series.partial]; norm_num
  rw [Series.partial_succ _ (by linarith)]
  push_cast at *; rw [ih (by linarith)]
  rw [dif_pos (by linarith)];
  nth_rw 3 [zpow_add₀ (by norm_num)]; ring

theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by
  unfold diverges converges convergesTo;
  simp_rw [Metric.tendsto_atTop]; push_neg
  intro L; use 1, (by norm_num);
  intro n
  choose N hN using exists_nat_gt (L+2)
  use max n (N+2), (by omega)
  rw [Series.example_7_2_4'a (by omega)]
  simp [dist];
  suffices 1 ≤ 2 ^ (max n (N+2) + 1) - 2 - L by
    rw [abs_of_pos (by positivity)]; exact this
  -- Move subtraction to the other side
  suffices L + 3 ≤ 2 ^ (max n (N+2) + 1) by linarith
  calc
    _ ≤ (N:ℝ) + 2 + 1 := by linarith
    _ ≤ (max n (↑N + 2) + 1 : ℤ) := by aesop
    _ ≤ 2 ^ (max n (N+2) + 1) := by
      generalize h : (max n (↑N + 2) + 1) = m
      lift m to ℕ using (by omega)
      apply n_le_pow_n


theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Finset.Icc m (n+1), a i = ∑ i ∈ Finset.Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert Finset.sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Finset.Icc m n, a i + ∑ i ∈ Finset.Icc (n+1) p, a i = ∑ i ∈ Finset.Icc m p, a i := by
  obtain ⟨k, rfl⟩ : ∃ k:ℕ, p = n + k := ⟨(p-n).toNat, by grind⟩
  induction' k with k hk
  · simp
  simp; rw [← add_assoc]
  rw [sum_of_nonempty (by linarith), sum_of_nonempty (by linarith)]
  rw [← add_assoc, hk (by linarith)]


-- Built-ins that I could've used, but I feel like it's more in the spirit of the textbook to do this using previous thms
#check Finset.sum_sdiff
#check Finset.Icc_subset_Icc_right

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  constructor
  · rintro ⟨L, hL⟩
    have hcauchy := hL.cauchySeq -- Cauchy if converges
    rw [Metric.cauchySeq_iff] at hcauchy
    peel hcauchy with e he h; choose N hN using h;
    use max (N+1) (s.m+1), (by grind)
    intro p hp q hq;
    by_cases hpq: q < p; simp_all; linarith -- Sum should have upper bound higher
    simp at hpq
    specialize hN q (by grind) (p-1) (by grind)
    simp [dist, Series.partial] at hN
    convert le_of_lt hN using 2
    have := @concat_finite_series (m:= s.m) (n:=p-1) (p:=q) (a:=s.seq) (by grind) (by linarith)
    rw [← this]; simp
  · intro h; apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro e he; choose N hN0 hN using h (e/2) (by positivity)
    use N; intro n hn m hm
    wlog hnm : n ≤ m generalizing n m; exact (dist_comm (s.partial n) _) ▸ this _ hm _ hn (by linarith)
    simp [dist, Series.partial]
    specialize hN (n+1) (by linarith) m hm
    nth_rw 2 [← concat_finite_series (n:=n) (by linarith) (by linarith)]; simp; linarith

/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  rw [converges_iff_tail_decay] at h
  rw [Metric.tendsto_atTop]
  intro e he; specialize h (e/2) (by positivity)
  peel h with N h; intro n hn; have := h.2 n hn n hn
  simp_all; linarith

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges :=  (decay_of_converges).mt h

set_option linter.unusedVariables false

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun n:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay; rw [Metric.tendsto_atTop]; push_neg; use 1/2, by norm_num
  intro N; use max 0 N, by simp
  simp; norm_num

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay; rw [Metric.tendsto_atTop]; push_neg; use 1/2, by norm_num
  intro N; use max 0 N, by simp
  simp; norm_num

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges



/-- Proposition 7.2.9 (Absolute convergence test) / Example 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  unfold Series.absConverges at h; rw [converges_iff_tail_decay] at *;
  rw [show s.abs.m = s.m by unfold abs; simp] at h;
  peel h with e he N hN p hp q hq h
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  convert h
  rw [abs_of_nonneg ?_]; congr 1; ext i; simp; intro h; simp_all [s.vanish]
  · apply Finset.sum_nonneg; intro i hi; simp_all; rw [if_pos (by linarith)]; apply abs_nonneg




theorem Series.abs_le' {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  have hconv := converges_of_absConverges h
  rw [sum_of_converges (convergesTo_sum hconv), sum_of_converges (convergesTo_sum h)]
  apply le_of_tendsto_of_tendsto (convergesTo_sum hconv).abs (convergesTo_sum h) -- le_mono from last chapter
  apply Filter.Eventually.of_forall -- Strengthen from ∀ᶠ to ∀

  intro z; simp [Series.partial]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _); apply le_of_eq
  apply Finset.sum_congr rfl; intro i hi; simp_all



theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ --Series using (-1)^n*(a n) converges
    Filter.atTop.Tendsto a (nhds 0)) := by -- a n converges
  -- This proof is written to follow the structure of the original text.
  constructor
  · intro h; have h' := h; apply decay_of_converges at h -- (-1)^n*(a n) must decay to 0
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    convert h using 2 with _ n -- Same distance from 0: abs eliminates (-1)^n
    simp [n.property]
  intro h -- a n decays to 0
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  -- Peel off last term
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  -- Peel off last two terms
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  -- Odd terms can only increase: you get a + term, then a - term that's equal or smaller
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  -- Even terms can only decrease: you get a - term, then a + term that's equal or smaller
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  -- Use induction to extrapolate claim3
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction' k with k ih
    · simp -- Same index
    apply le_trans ?_ ih;
    have : Even (N+2*k) := by grind -- Still even
    convert claim3 (by linarith) this using 1 -- So the next even term is ≤
    grind
  -- Use induction to extrapolate claim2
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    suffices S (N+2*k+1) ≥ S (N+1) by
      convert this; rw [claim0 hN]; rw [Odd.neg_one_zpow (Even.add_one h')]; linarith
    induction' k with k ih
    · simp
    have : Odd (N+2*k+1) := (Even.add_one (Even.add h' (by field_simp))) -- Still odd
    apply le_trans ih; rw [← ge_iff_le]
    convert claim2 (by linarith) this using 1
    grind
  -- The next odd term will always subtract, so it will always be ≤ the previous even term
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    rw [claim0 (by linarith)];
    rw [Odd.neg_one_zpow (by grind)]; simp [ha]
  -- Package why2, why3, why1 into a single claim
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  -- Every S n term is bounded above by S N, and below by
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    rcases Int.even_or_odd n with (h_even | h_odd)
    · obtain ⟨j, _⟩ := h_even.sub h'; obtain ⟨k, rfl⟩ : ∃ (k:ℕ), n = N + 2*k := ⟨j.toNat, by omega⟩
      refine ⟨le_trans (why2 hN h' k) (why3 hN h' k), why1 hN h' k ⟩
    obtain ⟨j, hk⟩ := h_odd.sub_even h'; obtain ⟨k, rfl⟩ : ∃ (k:ℕ), n = N + 2*k + 1 := ⟨j.toNat, by omega⟩
    refine ⟨(why2 hN h' k), le_trans (why3 hN h' k) (why1 hN h' k)⟩

  have why5' (N r : ℤ) (hN: Even N) (hr: r ≥ N) (hm : N ≥ m): |S r - S N| ≤ a ⟨ N+1, by grind ⟩ := by
    have ⟨h1,h2⟩:= why4 hm hN hr
    rw [_root_.abs_le']; simp; constructor <;> linarith

  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by
    have : Nonempty { n // n ≥ m } := ⟨m, by rfl⟩
    choose N hN using Metric.tendsto_atTop.mp h (ε/2) (by positivity)
    let X' := max (max 0 (N:ℤ)) m; let X :=  2*X'
    use X

    intro x hx y hy
    apply le_trans (dist_triangle (y:= S X) _ _)
    simp [dist];
    have why5'x := why5' X x (⟨X', by omega⟩) (by omega) (by omega)
    have why5'y := why5' X y (⟨X', by omega⟩) (by omega) (by omega)
    specialize hN (⟨X +1 , by omega⟩) (by apply Subtype.mk_le_mk.mpr; omega); simp at hN
    rw [abs_of_nonneg (by apply ha)] at hN
    rw [show ε = ε/2 + ε/2 by ring]; gcongr
    apply le_trans ?_ (le_of_lt hN); apply why5'x;
    apply le_trans ?_ (le_of_lt hN);
    convert why5'y using 1; exact abs_sub_comm (S X) (S y)

  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))





theorem Series.example_7_2_13a : example_7_2_13.converges := by
  unfold example_7_2_13;
  have := @Series.converges_of_alternating (m:=1) (a:=(fun n ↦ 1 / (n:ℤ)))
    (by intro n; simp; linarith [n.prop])
    (by intro n m hnm; simp only; gcongr; norm_cast;linarith [n.prop])

  conv at this => arg 1; arg 1; arg 1; simp [-one_div, mul_one_div]
  apply this.mpr
  have : Nonempty { n:ℤ // n ≥ 1 } := ⟨1, by grind⟩
  rw [Metric.tendsto_atTop]; intro e he; choose N hN using exists_nat_gt (1/e);
  use ⟨N+1, by grind⟩; intro n hn; simp [-one_div]
  have := n.prop
  obtain ⟨z, hz⟩ : ∃ z:ℤ, n = z := ⟨n, rfl⟩
  have hz' : (N : ℤ) + 1 ≤ z := by rw [← hz]; exact_mod_cast hn
  rw [hz] at ⊢ this
  simp at hn
  rw [one_div_lt (by rw [abs_of_pos (by simp;omega)];simp; omega) he]
  apply lt_trans hN
  rw [abs_of_pos (by finiteness)]
  lift z to ℕ using (by omega)
  simp; linarith

-- Using Lean's built-in theorem, because they explicitly reference a later
-- chapter for the proof, so I presume I shouldn't prove it here.
-- This requires an additional import, but I don't really know what else you want from me.

#check Real.summable_one_div_nat_pow

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  sorry

theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  sorry

instance Series.inst_add : Add Series where
  add a b := {
    m := max a.m b.m
    seq n := if n ≥ max a.m b.m then a.seq n + b.seq n else 0
    vanish n hn := by rw [lt_iff_not_ge] at hn; simp [hn]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HAdd.hAdd, Add.add]

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  sorry

theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by sorry

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The `convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  sorry

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by sorry

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := max a.m b.m
    seq n := if n ≥ max a.m b.m then a.seq n - b.seq n else 0
    vanish := by grind
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSub.hSub, Sub.sub]

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  sorry

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by sorry

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  sorry

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  sorry

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  sorry

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a (n+1) - a n):Series).convergesTo (a 0) := by
  sorry

/- Exercise 7.2.1  -/

def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  -- The first line of this proof should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  sorry


end Chapter7
