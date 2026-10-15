import Mathlib.Tactic
import Analysis.Section_7_3

/-!
# Analysis I, Section 7.4: Rearrangement of series

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Rearrangement of non-negative or absolutely convergent series.
-/

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) :
∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind



/-- Proposition 7.4.1.
Annotations added by GPT-6 Astra by OpenAI; original annotations retained.
Coercion compatibility repairs. Created by GPT-6 Astra by OpenAI.
-/
theorem Series.converges_of_permute_nonneg
    {a : ℕ → ℝ} (ha : (a : Series).nonneg) (hconv : (a : Series).converges) -- Assume nonnegative terms and convergence.
    {f : ℕ → ℕ} (hf : Function.Bijective f) : -- Let f be a permutation of the natural numbers.
    (fun n ↦ a (f n) : Series).converges ∧
      (a : Series).sum = (fun n ↦ a (f n) : Series).sum := by -- Prove convergence and preservation of the sum.
  -- This proof is written to follow the structure of the original text.

  /- Name the rearranged sequence and establish its nonnegativity.
     Series are indexed by integers, with the coerced sequence equal to zero
     at negative indices, so we distinguish negative and nonnegative indices. -/
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af : Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    simpa using ha (f n.toNat) -- Evaluate nonnegativity at the corresponding natural index.

  /- The partial sums are increasing because all terms are nonnegative.
     Let L and L' be their suprema. Convergence of the original series
     supplies the boundedness needed to use its supremum. -/
  set S := (a : Series).partial
  set T := (af : Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q :=
    (converges_of_nonneg_iff ha).mp hconv -- Bounded partial sums

  /- Reduce the theorem to two order-theoretic facts:
     the rearranged partial sums are bounded, and their supremum equals L.
     First explain why these facts imply the desired conclusion. -/
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  · -- The sups are equal to the sums, so making them equal means the sums are equal
    have Ssum : L = (a : Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      · use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af : Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      · use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    -- Bounding the other term will be our way to show its limit converges
    simp [← Ssum, ← Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1

  /- Prove every rearranged partial sum is at most L.
     For a nonnegative cutoff M, the finitely many original indices f(m)
     occurring in T M all lie below some N. Nonnegativity then gives
     T M ≤ S N ≤ L. -/
  have hTL (M : ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    · have hM' : M < 0 := by linarith  -- Empty partial sum
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    -- Our rearranged partial sum is a subset of some non-rearranged sum with higher index
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by -- Nat indexing
        simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by -- Set of f(n) indices
        symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by -- Bounded by larger set of indices
        apply Finset.sum_le_sum_of_subset_of_nonneg -- All indices ≤ N, so i ≤ N is a supset
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by
        simp [S, Series.partial]; symm; apply sum_eq_sum (N := N) a; positivity -- Recognize the natural-indexed sum as the original partial sum S N.
      _ ≤ L := by -- Upper bound
        apply le_ciSup _ (N : ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound] -- Every original partial sum lies below its bounded supremum.

  /- The preceding estimate supplies boundedness of T.
     This proves the first part of the sufficient condition, leaving L = L'. -/
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]

  /- Highly analogous to hTL -/
  have hSL' (N : ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    · have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    -- Our regular partial sum is a subset of some rearranged partial sum
    -- We need a big enough M to include all of regular sum
    -- Thus, every elem in sum needs to corresponding to some smaller f m
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      -- We take all the values that correspond to a val in the regular sum,
      -- and take the sup (maximum): thus, going from 0 to M, we'll hit all of them
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨_, hm, ?_⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    -- Show that we have a supset and thus an upper bound
    calc
      _ = ∑ n ∈ X, a n := by -- Nat indexing
        simp [S, Series.partial, Series.sum_eq_sum, hN, X]
      -- Include every index that outputs in the original sum
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        · intro h; obtain ⟨m, rfl, hm'⟩ := hM _ h; use m
        rintro ⟨_, ⟨_, _⟩, rfl⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by -- Subset of complete index i ≤ M
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by
        simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by -- Upper bound
        apply le_ciSup _ (M : ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]

  /- Each supremum bounds every partial sum defining the other.
     Consequently L ≤ L' and L' ≤ L, so the suprema are equal. -/
  linarith [ciSup_le hSL', ciSup_le hTL] -- Take suprema of the pointwise bounds and conclude equality.

#check Series.converges_qseries
#check Series.shift -- Astra reminded me about Series.shift

/-- Example 7.4.2 -/
theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by
  obtain ⟨L, hL⟩ := (Series.converges_qseries 2 (by simp)).mpr (by simp) -- Not identical, but close
  use L; convert (Series.shift hL (-1)) with z -- Index needs to be shifted
  simp [Series.ofNat]; funext z; split_ifs with hn <;> simp
  congr; rw [← Int.cast_natCast]; simp [hn]

#check Function.Involutive.bijective -- Suggested by astra (could do it other ways but tedious)

/-- Coercion compatibility repairs. Created by GPT-6 Astra by OpenAI. -/
theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
    have hq := (Series.converges_qseries 2 (by simp)).mpr (by simp)
    let f : ℕ → ℕ := fun n ↦ if Even n then n + 1 else n - 1 -- Rearrangement
    have := converges_of_permute_nonneg (f := f) (a := fun n : ℕ ↦ 1 / (n + 1 : ℝ)^2)
    specialize this (by intro n; simp; split_ifs with hn <;> positivity) Series.zeta_2_converges ?_
    · apply Function.Involutive.bijective; -- Easier way to do bijective in this case
      intro n; simp [f]
      by_cases h : Even n <;> simp [h]
      simp at h; choose m hm using h; grind
    convert this.1 using 3 with z;
    -- convert already gives a natural index; only its parity needs splitting.
    split_ifs with h1 <;> simp [f, h1] <;> field_simp
    ring; rw [Nat.cast_sub]; simp; simp [Odd] at h1; omega

/-- Coercion compatibility repairs. Created by GPT-6 Astra by OpenAI. -/
theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
    have hq := (Series.converges_qseries 2 (by simp)).mpr (by simp)
    let f : ℕ → ℕ := fun n ↦ if Even n then n + 1 else n - 1 -- Rearrangement
    have := converges_of_permute_nonneg (f := f) (a := fun n : ℕ ↦ 1 / (n + 1 : ℝ)^2)
    specialize this (by intro n; simp; split_ifs with hn <;> positivity) Series.zeta_2_converges ?_
    · apply Function.Involutive.bijective; -- Easier way to do bijective in this case
      intro n; simp [f]
      by_cases h : Even n <;> simp [h]
      simp at h; choose m hm using h; grind
    convert this.2.symm using 4 with z -- Basically the same just grab the other half
    -- convert already gives a natural index; only its parity needs splitting.
    split_ifs with h1 <;> simp [f, h1] <;> field_simp
    ring; rw [Nat.cast_sub]; simp; simp [Odd] at h1; omega

lemma Series.abs_coe_series (a : ℕ → ℝ) :
  (a : Series).abs = (fun n ↦ |a n| : Series) := by
  ext n; rfl -- Match the starting indices and compare the terms.
  by_cases hn : n ≥ 0 <;> simp [hn] -- Both series vanish at negative indices.

/-- Proposition 7.4.3 (Rearrangement of series).
Annotations added by GPT-6 Astra by OpenAI; original annotations retained.
Coercion compatibility repairs. Created by GPT-6 Astra by OpenAI.
-/
theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by

  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  /- Since |a n| is nonnegative, we can use 7.4.1 (permutation of nonnegative series) -/
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    simpa [L, abs_coe_series] using
      (converges_of_permute_nonneg (a := fun n ↦ |a n|)
        (by intro n; by_cases h : n ≥ 0 <;> simp [h])
        (by simpa [abs_coe_series] using ha) hf) -- Apply nonnegative rearrangement to the pointwise absolute values.

  /- Now, we need to handle the sum=sum goal: first, turn into into convergence-/
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L' -- One converges to the other
  . simp [sum_of_converges this, absConverges]
    simpa [abs_coe_series, af] using habs.1 -- Identify the rearranged absolute-value series.
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] -- Convert tendsTo into tractable form
  intro ε hε

  /-
  The goal from here on will be to take distance from partial rearranged sum, to partial original sum,
  to original series. We want to restrict both of these to ε/2.
  -/

  /-
    Later, we're gonna get the rearranged sum close the the original sum by looking at the tail left over
    from the difference.
    Since tails go to zero, we can use absolute value to bound them: we'll take the original absolute tail.
    That means we need to be at least as far enough to get that tail bounded by ε/2.
  -/
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁

  /-
  For dist(original partial sum → original series), by convergence definition,
  we can get within ε/2 distance, no additional work required.

  We'll consider our original sequence up to N.
  -/
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv -- The original partial sums tend to their series sum.
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv -- Extract the ε criterion for that limit.
    choose N hN using hconv _ (half_pos hε) -- Fix a convergence cutoff for ε/2.
    use max N N₁, (by grind); apply hN; grind -- Choose a cutoff satisfying both requirements.
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith -- The tail cutoff ensures N is nonnegative.

  /-
  We want the difference between the rearranged partial sum and the original partial sum to be limited to
  the tail.

  Above, we decided to consider the original partial sum up to N. So, the rearranged partial sum
  needs to include at least all of those terms, to cancel them out and leave only the tail.

  So, we'll lengthen the rearranged partial sum until it contains all of the original terms, with only
  rearranged terms left over.
  -/

  /-
  Each index m in rearranged-space will grab index (f m) in original-space.
  We want each n in original-space, which corresponds to (finv n) in rearranged-space.

  If we want all n in original-space, we need all (finv n) in rearranged-space.
  We can get this by taking a range that goes at least as high as the largest (finv n).
  -/
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id -- Sup is the max
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl -- Each inverse image lies below this maximum.
  choose M hM using this; use M; intro M' hM' -- Consider any rearranged cutoff M' ≥ M.
  have hM'_pos : M' ≥ 0 := by linarith -- Allow conversion to natural-number indices.
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    apply Finset.subset_iff.mpr -- Can't rw: not definitionally identical
    intro n hn; simp at hn ⊢; specialize hM n hn;
    use (finv n), (by apply le_trans hM; omega)
    unfold finv; apply Function.invFun_eq; apply hf.2 -- Surjective so we can invert here

  /- Split the rearranged sum into the canceled-out original and the extra original
     indices X.

     These extra indices X will be part of the tail we want to bound.-/
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by -- Switch to the original-index space
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by -- We can split the set into A and B\A in original-space, and thus two disjoint sums.
      convert Finset.sum_union _ using 2
      . simp [X, why]
      · infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto

  choose q' hq using X.bddAbove
  set q := max q' N.toNat

  /-
  X takes some tail elements up to q, so it's contained in a full tail [N+1,q]
  -/
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by
    intro n hn; simp; use (by simp [X] at hn; omega)
    unfold q; have := hq hn; grind

  /- Since this tail is bounded by ε/2, and the extra terms are part of this tail,
  the extra terms (and therefore the distance between sums) also bounded by ε/2. -/
  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc -- Distance between sums only includes these extra terms
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a -- Each term can at most contribute abs value
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp -- Extend from X extra terms to the full tail.
    _ ≤ ε/2 := by -- The full (absolute) tail is bounded by ε/2.
      convert ha (N.toNat+1) _ q _ <;> try omega -- Use abs tail bound
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2 -- Comparing ℕ and ℤ indices.
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

  /- The total error is at most the extra-tail error plus the
     original partial-sum error, giving ε/2 + ε/2 = ε. -/
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring



/-
Discrepancy from the book: this should be 1/(n+3). I don't care enough though, so I won't
bother changing it.
-/


/-- Example 7.4.4 -/
noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)





#check Series.converges_of_alternating
-- astra-suggested lemmas
#check tendsto_intCast_atTop_atTop
#check Filter.tendsto_add_atTop_iff_nat
#check Filter.tendsto_comp_val_Ici_atTop
#check tendsto_inv_atTop_zero

/-- Coercion compatibility repairs. Created by GPT-6 Astra by OpenAI. -/
theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by
  unfold Series.a_7_4_4;
  have := Series.converges_of_alternating (m:= 0) -- Invoke alternating properly
    (a:=(fun n ↦ (1 / ((n : ℤ) + 2 : ℝ))))
    (by intro n; have := n.prop; positivity)
    (by intro a b hab; simp_all; gcongr; have := a.prop; positivity)
  have := this.mpr -- The original converges by 1/n rule
    (by apply (Filter.tendsto_comp_val_Ici_atTop (f := fun n : ℤ ↦ 1 / (n + 2 : ℝ))).mpr; -- Deal with the awkwardness of {n | n ≥ m}
        rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff] -- Turn into nat, so we can use 1/n lemma
        have := (Filter.tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat -- Shift 1/n lemma by +2
        simpa)
  convert this -- Compare the coerced sequence with the alternating-series construction.
  simp [Series.ofNat]; funext z -- Expose the sequence functions and introduce their integer index.
  split_ifs with hz <;> try simp -- The negative case vanishes; the positive case may already be simplified.
  lift z to ℕ using hz; field_simp



#check Nat.strong_induction_on
-- Couldn't find an Icc equivalent to this lemma so I think I'll go with Ico
-- We had concat_finite_series in 7.1 but we weren't given that as import so meh
#check Finset.sum_Ico_consecutive
#check Finset.sum_Ico_succ_top
#check Series.sum_eq_sum

#check Finset.sum_insert

/-- Coercion compatibility repairs. Created by GPT-6 Astra by OpenAI. -/
theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by
  apply lt_of_lt_of_le (b:= 1/6) (by simp) -- 1/2 - 1/3 = 1/6 is as low as we go: any longer series add a positive amount
  have h := Series.ex_7_4_4_conv
  -- All terms are ge 1/6, so the limit ge 1/6
  apply ge_of_tendsto (Series.convergesTo_sum h)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℤ)] with N hN -- Start with first two terms, remaining terms are nonneg
  lift N to ℕ using (by omega) -- We're gonna do induction
  -- First two terms add to 1/6, and the remainder are nonnegative.
  suffices ht : 0 ≤ ∑ k ∈ Finset.Ico 2 (N + 1), a_7_4_4 k by
    simp only [Series.partial, Series.ofNat_m, Series.ofNat_seq] -- Expose the start index and terms before reindexing.
    rw [Series.sum_eq_sum _ (by simp)]; simp only [Int.toNat_natCast] -- Switch to nat
    rw [show Finset.Iic N = Finset.Ico 0 (N + 1) by bound]
    rw [← Finset.sum_Ico_consecutive (n:=2) _ (by simp) (by omega)] -- Split
    rw [← add_zero (1/6)]; gcongr; norm_num
  norm_cast at hN
  induction' N using Nat.strong_induction_on with N ih -- Strong induction so we can take off more than 1 term
  by_cases hN: N+1 ≤ 2
  · simp_all
  push_neg at hN
  by_cases hpar : Even N
  · rw [Finset.sum_Ico_succ_top (by linarith)] -- Split off one term that's positive
    specialize ih (N-1) (by omega) (by omega); simp [show N - 1 + 1 = N by omega] at ih
    rw [← add_zero 0]; gcongr; unfold a_7_4_4; simp [hpar]; positivity
  rw [← Finset.sum_Ico_consecutive (n:=N-1) _ (by grind) (by grind)]
  simp at hpar; choose k hk using hpar; have: N > 2 := by grind -- N > 2 if odd and N ≥ 2
  specialize ih (N-2) (by omega) (by omega); simp [show N - 2 + 1 = N - 1 by omega] at ih
  rw [← add_zero 0]; gcongr;
  rw [Finset.sum_Ico_succ_top (by omega), show N = N - 1 + 1 by omega];
  simp [a_7_4_4]
  rw [Even.neg_one_pow (by bound), Odd.neg_one_pow (by bound)];
  ring_nf; bound


/-
This seems horribly tedious for no benefit so I'm just gonna skip it.
-/

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 2*n - (n/3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by sorry

theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by sorry

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by sorry

lemma Series.absSeries_nonneg {s: Series}: (s.abs).nonneg := by
  intro n; unfold abs; simp; split_ifs <;> simp




/-- Exercise 7.4.1 -/
theorem Series.absConverges_of_subseries {a:ℕ → ℝ}
(ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by
  unfold absConverges abs at *
  choose A hA using ha
  rw [Series.converges_of_nonneg_iff (Series.absSeries_nonneg)]
  use A; intro z
  apply le_trans (b:= (a:Series).abs.partial (f z.toNat)); swap
  · rw [← Series.sum_of_converges hA]; apply partial_le_sum_of_nonneg (Series.absSeries_nonneg) ⟨A,hA⟩
  by_cases hz : z < 0
  · simp_all; conv => lhs; simp [Series.partial, hz]
    apply Series.partial_nonneg (Series.absSeries_nonneg)
  simp [Series.partial]
  lift z to ℕ using (by omega);

  let b n := |if 0 ≤ n then a n else 0|
  let c n := b (f n)

  /-
  This one sucked because it took me a while to realize that I needed to use
  `convert_to` so that Lean could recognize it as an instance of for `sum_eq_sum` to use.
  -/
  convert_to (∑ x ∈ Finset.Icc 0 (↑z : ℤ), if 0 ≤ x then (c x.toNat) else 0) ≤
    ∑ x ∈ Finset.Icc 0 (↑(f (↑z : ℤ).toNat) : ℤ), if 0 ≤ x then (b x.toNat) else 0
  · unfold c b; congr; ext i; split_ifs with h h <;> simp; linarith
  · unfold b; congr; ext i; split_ifs with h h <;> simp; linarith
  rw [sum_eq_sum _ (by omega), sum_eq_sum _ (by omega)]
  simp; unfold c
  rw [← Finset.sum_image]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; simp_all; obtain ⟨w, h, rfl⟩ := hn; exact (StrictMono.le_iff_le hf).mpr h
    intros; unfold b; apply abs_nonneg
  apply Set.injOn_of_injective; exact StrictMono.injective hf

/-
You can still accomplish 7.4.1 using injectivity instead of strictmono. You just need to, instead
of using f(z) as the upper bound, you just take the image f (ℕ_z) and you use the upper bound of that
instead.

For time's sake, I'm going to skip this.
-/

/-- Exercise 7.4.1 -/
theorem Series.absConverges_of_subseries' {a:ℕ → ℝ}
(ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: f.Injective) :
  (fun n ↦ a (f n):Series).absConverges := by
  sorry


#check Series.converges_of_permute_nonneg

/-
This next theorem would benefit from being able to convert abs sequences
at the direct level of sequences, based on 7.4.1's result being in terms of
ℕ → ℝ sequences, rather than series.
-/
set_option pp.coercions.types true in
/-- Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
    and expressing `a n` as the difference of `a n + |a n|` and `|a n|`. -/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (haabs_conv : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum := by

  have hconv := converges_of_absConverges haabs_conv
  rw [absConverges, abs_coe_series a] at haabs_conv

  set aabs : ℕ → ℝ := fun n ↦ |a n|
  set aplus : ℕ → ℝ := fun n ↦ a n + |a n|
  set sabs : Series := (aabs : Series)
  set saplus : Series := (aplus : Series)
  set sa : Series := (a : Series)
  set sa_f : Series := (fun n ↦ a (f n) : Series)
  set saplus_f : Series := (fun n ↦ aplus (f n) : Series)
  set sabs_f : Series := (fun n ↦ aabs (f n) : Series)

  have ⟨hplus_conv, hplus_sum⟩ := Series.add hconv haabs_conv
  have hplus_conv : (aplus : Series).converges := by rwa [← add_coe a aabs]
  refold_let saplus at *

  have haa:= converges_of_permute_nonneg (a := aabs)
    (by intro n; simp; split_ifs with n <;> simp [aabs]) haabs_conv hf
  have hap := converges_of_permute_nonneg (a := aplus)
    (by intro n; simp; split_ifs with n; apply add_abs_nonneg; simp) hplus_conv hf
  refold_let sabs saplus sa sa_f saplus_f sabs_f at *

  constructor
  · rw [absConverges, abs_coe_series (fun n ↦ a (f n))] -- Since we used aabs instead of a directly, we need conversion
    apply haa.1

  have h (b: ℕ → ℝ) : (b : Series) = (fun n ↦ b n + |b n| : Series) - (fun n ↦ |b n| : Series) := by
    rw [sub_coe (fun n ↦ b n + |b n|) (fun n ↦ |b n|)]; simp
  unfold sa sa_f; rw [h a, h ((fun n ↦ a (f n)))]
  refold_let sabs saplus sa sa_f saplus_f sabs_f at *

  -- Split up sums so each can use converges_of_permute separately
  rw [(Series.sub hplus_conv haabs_conv).2,   (Series.sub hap.1 haa.1).2]
  rw [haa.2, hap.2]

end Chapter7
