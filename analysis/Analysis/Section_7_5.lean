import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.LiminfLimsup

/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Chapter7

open Filter Real EReal

#check Filter.limsup
#check Filter.atTop
--#check atTop

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite.
Annotations added by GPT-6 Sol (from OpenAI); original proof preserved.
-/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.

    /- Name the extended-real limsup. Every root is nonnegative, so a frequently
       valid lower bound of zero also bounds its limsup from below. -/
    set α':EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n:ℝ)):ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity

    /- Since α' is below 1 it is not ⊤, and since it is nonnegative it is
       not ⊥. Thus coe_toReal identifies it with the real number α.
       The two contraposition branches discharge those endpoint exclusions. -/
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos

    /- Choose a positive margin halfway between α and 1. The resulting
       geometric base α + ε is both positive and strictly less than 1. -/
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith

    /- The limsup bound makes every sufficiently late nth root smaller than
       α + ε. Increase the cutoff to include the series starting index s.m
       and to ensure all relevant integer exponents are positive. -/
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)

    /- Raise the eventual root inequality to the positive integer n. The
       first calc step recovers |s.seq n| by multiplying the exponents;
       the second converts between natural powers and integer powers. -/
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega

    /- Moving start index from s.m to N, so we can use |s.seq n| ≤ (α + ε)^n.
       N is an integer, but `converges_from` requires a natural-number offset k = (N - s.m).toNat.
       The geometric series with base α + ε converges because that base is between 0 and 1. -/
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom

    /- Compare the tail starting at N (s.from N) termwise with the convergent
       geometric tail.
       |s.seq n| ≤ (α + ε)^n means the geometric tail bounds its absolute values above.
       The geometric tail converges, so the tail of s.from N converges absolutely. -/
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega

    /- Convergence is unchanged by removing the first k terms. Unfold
       absolute convergence and identify the two tails pointwise. The
       cases account for indices before s.m and before the cutoff N. -/
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> grind



/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) > 1) : s.diverges := by
    -- h : Frequently we'll find 1 < |s n|^(1/n), because 1 < limsup
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    -- If s → 0, then (this: eventually |s n| < 1 consistently)
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    -- This means frequently, both are true
      -- Once we're past the "eventually" threshold, all vals will have |s n| < 1
      -- Frequently beyond that point, we'll find vals where 1 < |s n|^(1/n)
      -- So, one value will have both |s n| < 1 and 1 < |s n|^(1/n)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_:0 < 1/(n:ℝ)) <;> try positivity
    -- Contradiction
    rw [show (1:EReal) = (1:ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.diverges := by
    use (fun _ ↦ 1: ℕ → ℝ); constructor
    · rw [LinearOrderedAddCommGroup.tendsto_nhds]; intro e he
      rw [eventually_atTop]; use 0; intro z hz; simpa [hz]
    exact example_7_2_7


/-- Lemma 7.5.2 / Exercise 7.5.1.
Annotations added by GPT-6 Sol (from OpenAI); original proof preserved.

Split off as part of ratio_ineq: no reason to make the theorem so big??
-/
theorem Series.ratio_ineq' {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  /- Let L' be the limsup of consecutive ratios. If L' is +∞, the desired
     upper bound is immediate. -/
  set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
  by_cases hL : L' = ⊤; simp [hL]

  /- Ratios are eventually positive, so their limsup is nonnegative: L' ≠ −∞ .
     L' ≠ −∞ or ∞ so we can coerce to (L : Real). -/
  have hL'pos : 0 ≤ L' := by
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N; use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := by intro h; simp_all
  set L := L'.toReal
  have hL' : L' = L := (coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos

  /- If x ≤ L + ε for any ε, then x ≤ L.
     Mathlib uses y (y > L) instead of L + ε, so we convert.
  -/
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤; simp [hy']
  have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by grind
  replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
  rw [this]

  /- L + ε > limsup, so eventually the ratios are below L + ε.
    Choose N large enough to satisfy eventual ratio, eventual positivity, and N > 0.-/
  have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [eventually_atTop] at this; choose N' hN using this
  set N := max N' (max m 1)
  have (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this; norm_cast at hN; order

  /- Induction to prove c(n) ≤ A(L+ε)^n, where A = c(N)(L+ε)^(-N).-/
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by specialize hpos N (by omega); positivity
  have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
    obtain ⟨k, rfl⟩ : ∃ k:ℕ, n = N + k := ⟨ (n - N).toNat, by omega ⟩
    induction' k with k ih
    · simp [A]; field_simp
    push_cast; repeat rw [← add_assoc]
    -- Concat hN with ih (ih needs a factor of (L+ε))
    trans c (N + k) * (L+ε)
    · apply le_of_lt; specialize hpos (N+k) (by omega)
      specialize hN (N + k) (by omega); norm_cast at hN;
      exact (div_lt_iff₀' hpos).mp (hN)
    specialize ih (by omega);
    have ih' : c (N + k) * (L+ε) ≤ A * (L+ε)^(N + k) * (L+ε) := by bound
    convert ih' using 1;
    rw [zpow_add_one₀ (by positivity)]; ring

  /- Take positive 1/n powers of the geometric bound. The integer exponent
     n cancels with 1/n, leaving c(n)^(1/n) ≤ A^(1/n)(L+ε). -/
  have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
        apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
      _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←rpow_intCast, ←rpow_mul (by positivity)]
        convert rpow_one _
        field_simp

  /- Pass the eventual root inequality to limsups. Bound the limsup of the
     product by the product of limsups. Finally A^(1/n) → 1 because A > 0
     and 1/n → 0, so the right-hand side becomes L + ε = y. -/
  calc
    _ ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
      apply limsup_le_limsup <;> try isBoundedDefault
      unfold EventuallyLE; rw [eventually_atTop]
      use N
    _ ≤ (atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal))) * (atTop.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal))) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Frequently.of_forall; intros; positivity
      . apply Eventually.of_forall; simp; positivity
      . simp [-coe_add]
      simp [-coe_add]; grind
    _ = (L+ε:ℝ) := by
      simp; convert one_mul _
      apply Tendsto.limsup_eq
      convert Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
      . apply continuous_coe_real_ereal.tendsto'; norm_num
      convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
      . apply (continuous_const_rpow (by positivity)).tendsto'; simp
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop


/-
This task is weird in Lean. It's basically just mirroring a bunch of the
provided proof, which is tedious but not terrible.
But also, there's a lot of weird technical stuff. Like continuity shows up even though we haven't done it?? Strange.
At least that can be copy-pasted.
-/

/-
Confession: because of this, I just ended up letting the AI do it.
It's just not worth it.
This is one of the only cases where I've done this.

Interestingly, they did it a bit differently:
- Never bother to introduce ε
- "0 ≤ ·" uses the other term now because it's the stronger statement
- A^(1/n) → 1 is given its own `have` statement, which makes it a little more readable.
-/

#check le_of_forall_lt_imp_le_of_dense -- If even tiniest bit below a₁ is always ≤ a₂, then a₁ ≤ a₂.
#check Filter.eventually_lt_of_lt_liminf -- Turn a value below the liminf into an eventual lower bound.
#check Filter.Tendsto.liminf_eq -- Identify the liminf of a convergent sequence with its limit.
#check Filter.liminf_le_liminf -- Pass an eventual pointwise inequality to liminfs.

/-- Lemma 7.5.2 / Exercise 7.5.1.
Annotations and proof added by GPT-6 Astra (from OpenAI).
-/
theorem Series.ratio_ineq'' {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
    := by
  /- Let L' be the liminf of consecutive ratios. The roots are eventually
     nonnegative, so a nonpositive lower bound for L' is immediate. -/
  set L' := atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal))
  have hroot : (0:EReal) ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
    apply le_liminf_of_le (by isBoundedDefault) -- Roots are eventually nonnegative.
    rw [eventually_atTop]
    refine ⟨max m 1, fun n hn ↦ ?_⟩
    have hc := hpos n (by omega)
    positivity

  /- If every y < L' is below the root liminf, then L' is below the root
     liminf. For positive y, we can coerce y to a real number B. -/
  apply le_of_forall_lt_imp_le_of_dense -- Test every strict lower bound of the ratio liminf.
  intro y hy
  by_cases hy0 : y ≤ 0
  · exact hy0.trans hroot
  have hypos : 0 < y := lt_of_not_ge hy0
  have hyTop : y ≠ ⊤ := ne_top_of_lt hy
  have hyreal : y = (y.toReal:EReal) := (coe_toReal hyTop (ne_bot_of_gt hypos)).symm
  set B := y.toReal
  have hB : 0 < B := by rwa [hyreal, EReal.coe_pos] at hypos

  /- B < liminf, so eventually the ratios are above B.
     Choose N large enough to satisfy eventual ratio, eventual positivity, and N > 0. -/
  have hev := eventually_lt_of_lt_liminf hy (by isBoundedDefault)
  rw [eventually_atTop] at hev
  obtain ⟨N', hN'⟩ := hev
  set N := max N' (max m 1)
  have hratio (n:ℤ) (hn : n ≥ N) : B ≤ c (n+1) / c n := by
    have hn' : N' ≤ n := by omega
    have := hN' n hn'
    rw [hyreal, EReal.coe_lt_coe_iff] at this
    exact this.le

  /- Induction to prove A B^n ≤ c(n), where A = c(N) B^(-N). -/
  set A := c N * B^(-N)
  have hA : 0 < A := by
    have := hpos N (by omega)
    positivity
  have hgeom (n:ℤ) (hn : n ≥ N) : A * B^n ≤ c n := by
    obtain ⟨k, rfl⟩ : ∃ k:ℕ, n = N + k := ⟨(n-N).toNat, by omega⟩
    induction' k with k ih
    · simp only [Nat.cast_zero, add_zero]
      change c N * B^(-N) * B^N ≤ c N
      rw [zpow_neg, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero N hB.ne')] -- The geometric bound is exact at the starting index.
      simp
    push_cast
    repeat rw [← add_assoc]
    -- Combine the induction hypothesis with the lower ratio bound (adding one factor of B).
    calc
      A * B ^ (N + ↑k + 1) = A * B ^ (N + ↑k) * B := by
        rw [zpow_add_one₀ hB.ne'] -- Split off one ratio factor.
        ring
      _ ≤ c (N+k) * B := by
        specialize ih (by omega)
        exact mul_le_mul_of_nonneg_right ih hB.le
      _ ≤ c (N+k+1) := by
        have hc := hpos (N+k) (by omega)
        have hr := hratio (N+k) (by omega)
        simpa [mul_comm] using (le_div_iff₀ hc).mp hr

  /- Take positive 1/n powers of the geometric bound. The integer exponent
     n cancels with 1/n, leaving A^(1/n) B ≤ c(n)^(1/n). -/
  have hrootgeom (n:ℤ) (hn : n ≥ N) :
      ((A^(1/(n:ℝ)) * B:ℝ):EReal) ≤ ↑((c n)^(1/(n:ℝ)):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hnpos : 0 < n := by omega
    have hnreal : (0:ℝ) < n := by exact_mod_cast hnpos
    calc
      _ = A^(1/(n:ℝ)) * (B^n)^(1/(n:ℝ)) := by
        congr 1
        rw [← rpow_intCast, ← rpow_mul (by positivity)]
        have he : (n:ℝ) * (1/(n:ℝ)) = 1 := by field_simp
        rw [he, rpow_one]
      _ = (A * B^n)^(1/(n:ℝ)) := (mul_rpow (by positivity) (by positivity)).symm
      _ ≤ _ := by
        apply rpow_le_rpow (by positivity) (hgeom n hn) -- Positive roots preserve the bound.
        positivity

  /- A^(1/n) → 1 because A > 0 and 1/n → 0, so the lower geometric
     bound tends to B = y. -/
  have hAroot : Tendsto (fun n:ℤ ↦ A^(1/(n:ℝ))) atTop (nhds 1) := by
    have hp : Tendsto (fun x:ℝ ↦ A^x) (nhds 0) (nhds 1) := by
      apply (continuous_const_rpow (by positivity)).tendsto' -- Powers of a positive base are continuous.
      simp
    have hi : Tendsto (fun n:ℤ ↦ (n:ℝ)⁻¹) atTop (nhds 0) := by
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop -- Reciprocal indices tend to zero.
    simpa [one_div] using hp.comp hi
  have hmul : Tendsto (fun n:ℤ ↦ A^(1/(n:ℝ)) * B) atTop (nhds B) := by
    simpa using hAroot.mul_const B

  /- Pass the eventual root inequality to liminfs. The liminf of the
     geometric bound is y, so y is below the root liminf. -/
  calc
    y = atTop.liminf (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * B:ℝ):EReal)) := by
      rw [hyreal]
      apply (Tendsto.liminf_eq ?_).symm -- The geometric factor tends to one.
      exact continuous_coe_real_ereal.tendsto B |>.comp hmul
    _ ≤ atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ)) := by
      apply liminf_le_liminf (h := ?_) (by isBoundedDefault) (by isBoundedDefault) -- Pass the eventual root bound to liminf.
      rw [eventually_atTop]
      exact ⟨N, fun n hn ↦ hrootgeom n hn⟩

/-- Lemma 7.5.2 / Exercise 7.5.1.
-/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  refine ⟨ ratio_ineq'' m hpos, liminf_le_limsup ?_ ?_, ratio_ineq' m hpos ⟩ <;> try isBoundedDefault



/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test)-/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp



/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
    use (fun _ ↦ 1: ℕ → ℝ), (by field_simp); constructor
    · rw [LinearOrderedAddCommGroup.tendsto_nhds]; intro e he
      rw [eventually_atTop]; use 0; intro n hn; simp [hn]
      rw [if_pos (by omega)]; norm_num; exact he
    exact example_7_2_7

#check Series.converges_qseries

/-
Lemmas suggested by GPT-6 Sol
-/
#check Tendsto.congr'
#check Tendsto.pow
#check eventually_ge_atTop
#check Tendsto.const_div_atTop

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3.
Created by GPT-6 Astra by OpenAI. -/
theorem Series.ratio_test_inconclusive'_ : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
  let s : Series := mk' (m := 1) fun n ↦ 1 / (n : ℝ) ^ 2 -- Choose the convergent square reciprocal series.
  refine ⟨s, ?_, ?_, ?_⟩ -- Prove nonvanishing, the ratio limit, and absolute convergence.
  · intro n hn
    simp [s, hn] -- Evaluate the term at an index beyond the starting point.
    positivity -- The denominator is a positive square.
  · have hlim : Filter.Tendsto (fun n : ℤ ↦ (1 - 1 / ((n : ℝ) + 1)) ^ 2)
        atTop (nhds 1) := by
      have hden : Filter.Tendsto (fun n : ℤ ↦ (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_intCast_atTop_atTop -- The shifted denominator grows without bound.
      convert ((tendsto_const_nhds.sub (hden.const_div_atTop 1)).pow 2) using 1 <;> norm_num -- The reciprocal tends to zero.
    apply hlim.congr' -- Identify the ratio with the auxiliary expression eventually.
    filter_upwards [Filter.eventually_ge_atTop (1 : ℤ)] with n hn -- Work after the series starting index.
    simp [s, hn, show 1 ≤ n + 1 by omega, abs_inv, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] -- Remove absolute values from positive reciprocals.
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega) -- The index is at least one.
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity -- The next index is positive.
    field_simp -- Simplify the identity using the nonzero denominators.
  · have hsabs : s.abs = s := by
      apply Series.ext -- Compare the starting index and every term.
      · rfl
      · funext n -- Reduce sequence equality to a pointwise identity.
        by_cases hn : 1 ≤ n -- Separate genuine terms from the zero prefix.
        · simp [s, hn] <;> positivity -- Every term of the squared reciprocal series is nonnegative.
        · simp [s, hn] -- Terms before the starting index vanish.
    rw [absConverges, hsabs] -- Absolute convergence reduces to convergence of this nonnegative series.
    simpa [s] using (Series.converges_qseries 2 (by norm_num)).2 (by norm_num) -- Apply the earlier q-series criterion.


lemma Series.plus_one_atTop : Tendsto (fun (n : ℤ) ↦ (↑n : ℝ) + 1) atTop atTop := by
  apply tendsto_atTop_add_const_right; exact tendsto_intCast_atTop_atTop

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
    let s := ((fun n ↦ 1/(n)^2 : ℕ → ℝ):Series).from 1
    use s, (by intro n hn; simp_all [s]; constructor<;>linarith)
    constructor
    · apply Tendsto.congr' (f₁ := (fun (n:ℤ) ↦ ((1-1/(n+1):ℝ )^2) )) -- Convert inside of limit
      · filter_upwards [eventually_ge_atTop (1 : ℤ)] with n hn -- Makes n natural & positive
        lift n to ℕ using (by omega);
        simp_all [s]; repeat rw [if_pos] <;> try linarith
        repeat rw [abs_of_pos (by positivity)]
        field_simp
      nth_rw 4 [← one_pow (n:=2)]; apply Tendsto.pow -- Rearrange until the limit is solved
      nth_rw 4 [← sub_zero (a:=1)]; apply Tendsto.sub (tendsto_const_nhds)
      apply Tendsto.const_div_atTop plus_one_atTop
    have := (Series.converges_qseries 2 (by linarith)).mpr (by norm_num)
    unfold absConverges; convert this using 1; ext i; simp [s];
    simp [s]; split_ifs with h1 h2;
    · lift i to ℕ using (by linarith); simp
    · linarith
    · rfl


lemma Series.nplus1_div_n_tendsto : atTop.Tendsto (fun (n:ℤ) ↦ ((n+1:ℤ):ℝ) / (n:ℝ)) (nhds 1) := by
    apply Tendsto.congr' (f₁ := (fun (n:ℤ) ↦ (1 / (n:ℝ))+1))
    · filter_upwards [eventually_ge_atTop (1 : ℤ)] with n hn -- Start at 1 for nonzero nat
      push_cast; field_simp; apply add_comm
    nth_rw 3 [← zero_add 1]; apply Tendsto.add -- Solve limit
    apply Tendsto.const_div_atTop tendsto_intCast_atTop_atTop
    apply tendsto_const_nhds


/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) := by
  have ⟨hinf, hinfsup, hsup⟩:= Series.ratio_ineq (c := ( · )) 1
    (by intro n hn; positivity)
  suffices atTop.Tendsto (fun (n:ℤ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) by
    simpa using this.comp (tendsto_natCast_atTop_atTop (R := ℤ)) -- Precomp a ℕ → ℤ conversion
  have hlim_rat:= Series.nplus1_div_n_tendsto -- ((n+1)/n) → 1
  rw [← EReal.tendsto_coe] at *; -- EReal-ℝ conversions
  have hinf_rat := Tendsto.liminf_eq hlim_rat -- Turn lim into liminf
  have hsup_rat := Tendsto.limsup_eq hlim_rat -- Turn lim into limsup
  apply tendsto_of_le_liminf_of_limsup_le ?_ ?_ (by isBoundedDefault) -- if liminf and limsup both go to 1, lim=1
  apply le_trans ?_ hinf; rw [hinf_rat]
  apply le_trans hsup ?_ ; rw [hsup_rat]

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges' (q: ℝ ) (hq : q > 0):
  atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(q / n : ℝ)) (nhds 1) := by
  let f := fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))
  apply Tendsto.congr' (f₁ := (fun (n:ℕ) ↦ (f n)^q))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [← rpow_mul (by positivity)]
    ring_nf
  rw [show 1 = (1:ℝ)^q by simp]
  apply Tendsto.rpow_const ?_ (by grind)
  unfold f; exact root_self_converges


/-
This exercise was originally placed further above in the text, but I think it's in the spirit
to be listed here, since the desired proof result to use is above.
-/

#check Series.converges_qseries

theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
    let s := ((fun n ↦ 1/(n)^2 : ℕ → ℝ):Series).from 1; use s;
    constructor
    · suffices atTop.Tendsto (fun (n:ℕ) ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) by -- ℕ indexing
        simpa [← Nat.map_cast_int_atTop, tendsto_map'_iff]
      apply Tendsto.congr' (f₁ := (fun (n:ℕ) ↦ 1/(n:ℝ)^(2 / (n:ℝ)))) -- Can use root_self_converges'
      · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        simp [s, -one_div, hn]; rw [abs_of_pos (by bound)]
        rw [← Real.rpow_natCast (n : ℝ) 2, Real.div_rpow (by positivity) (by positivity)];
        rw [← rpow_mul (by positivity)]; simp; ring_nf
      nth_rw 2 [← div_one 1];
      apply Tendsto.div tendsto_const_nhds ?_ (by norm_num)
      apply root_self_converges' 2 (by positivity)
    have hsabs: s = s.abs := by
      ext i; simp; unfold s abs; simp; split_ifs with h;
      · rw [abs_of_nonneg]; positivity
      simp; simp
    have := (Series.converges_qseries 2 (by linarith)).mpr (by norm_num)
    unfold absConverges; convert this using 1; ext i; simp [s];
    rw [← hsabs]; simp [s]
    split_ifs with h1 h2;
    · lift i to ℕ using (by linarith); simp
    · linarith
    · rfl


/-
Edit to match the textbook: absConverges, not converges
-/

lemma Series.comm_abs_from (s: Series) (n: ℤ) : (s.from n).abs = (s.abs).from n := by
  ext i; simp
  simp; split_ifs with h1 h2; rfl; tauto; rfl

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).absConverges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
  set w := (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series)
  suffices w.absConverges by -- The former goal implies the latter
    refine ⟨this, ?_⟩; have hconv:= converges_of_absConverges this
    simpa using -- Need the natCast so the two sides are indexed the same
    (Series.decay_of_converges hconv).comp (tendsto_natCast_atTop_atTop (R := ℤ))

  set s := w.from 1
  suffices s.absConverges by -- Using from 1 for positivity
    subst s; unfold absConverges at *
    rw [comm_abs_from w 1] at this
    rw [Series.converges_from _ 1]
    convert this

  by_cases hx0 : x = 0 -- Zero function is gonna sum to 0
  · subst hx0; use 0;
    unfold convergesTo; convert tendsto_const_nhds using 1
    unfold Series.partial; ext i;
    apply Finset.sum_eq_zero; simp [s,w]; intros; right; linarith

  apply ratio_test_pos ?_ ?_ -- Ratio test: check positivity
  · intro n hn; simp [s] at *; lift n to ℕ using (by linarith); simp [w] at *
    simp [hn]; constructor
    positivity; tauto

  have htend : atTop.Tendsto (fun n ↦ ↑(|s.seq (n + 1)| / |s.seq n|)) (nhds |x|) := by -- Ratio test condition
    simp [s, w]; apply Tendsto.congr' (f₁ := fun (n:ℤ) ↦ ((n+1)/n)^q*|x|)
    · filter_upwards [eventually_ge_atTop (1 : ℤ)] with n hn
      lift n to ℕ using (by linarith); simp
      repeat rw [if_pos (by linarith)]
      rw [div_rpow (by positivity) (by positivity), _root_.abs_mul, _root_.abs_mul];
      norm_cast at hn; field_simp
      nth_rw 2 [abs_of_pos (by positivity)]; nth_rw 3 [abs_of_pos (by positivity)];
      ring
    nth_rw 2 [← one_mul |x| ]
    apply Filter.Tendsto.mul
    · nth_rw 2 [show (1:ℝ) = 1^q by simp]; apply Tendsto.rpow_const ?_ (by grind)
      convert nplus1_div_n_tendsto; norm_cast
    apply tendsto_const_nhds
  rw [← EReal.tendsto_coe] at *
  have := Tendsto.limsup_eq htend
  rw [this]; norm_cast

end Chapter7
