import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue
--import Mathlib.Tactic.TacticAnalysis

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals `EReal`, particularly with regard to the supremum
  operation `sSup` and infimum operation `sInf`.

-/
--set_option linter.tacticAnalysis.tryAtEachStepGrind true -- This is the only reason for the extra above import
open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast

lemma EReal.lt_top (x:ℝ) : (x:EReal) < ⊤ := by rw [lt_iff]; simp


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := lt_top 3


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := by simp


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

lemma EReal.ge_bot (x:EReal) : ⊥ ≤ x := by rw [le_iff]; tauto
lemma EReal.le_top (x:EReal) : x ≤ ⊤ := by rw [le_iff]; tauto

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by
  rw [le_iff]; rcases EReal.def x with h | rfl | rfl
  · left; obtain ⟨x', rfl⟩ := h; use x', x';
  tauto;tauto

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by
  rw [lt_iff, gt_iff_lt, lt_iff]
  rcases EReal.def x with hx | rfl | rfl <;> rcases EReal.def y with hy | rfl | rfl
  any_goals simp only [ge_bot, le_top]
  any_goals tauto
  obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
  rw [← lt_iff, ← gt_iff_lt, ← lt_iff];
  rcases lt_trichotomy x y with h | rfl | h <;> simp only [EReal.coe_lt_coe_iff] <;> tauto

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by rw [lt_iff]; tauto

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by rw [gt_iff_lt, lt_iff]; tauto

theorem EReal.antisymm (x y:EReal) : x ≤ y → y ≤ x → x = y := by
  simp [le_iff]; intro h1 h2
  rcases h1 with ⟨x, rfl, y, rfl, hxy⟩ | rfl | rfl <;>
  rcases h2 with ⟨x', hx, y', hy, hyx⟩ | hx | hy
  any_goals simp_all
  linarith


/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by
  simp [lt_iff]; intro h1 h2 h3; exfalso
  apply h2; apply antisymm <;> assumption

/-
Wasting too much conceptual time where I could just simp
-/

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  rw [le_iff] at *;
  by_cases hz : z = ⊤; tauto; by_cases hx : x = ⊥; tauto; simp [hz, hx] at hxy hyz ⊢
  simp [show y ≠ ⊤ by intro h; simp_all] at hxy; simp [show y ≠ ⊥ by intro h; simp_all] at hyz
  obtain ⟨x', rfl, y', rfl, hxy'⟩ := hxy; obtain ⟨y'', hx, z', rfl, hyz'⟩ := hyz
  simp at hx; subst hx; refine ⟨x', rfl, z', rfl, by linarith⟩

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  rw [le_iff] at *; rcases hxy with ⟨x', y', rfl, rfl, hxy'⟩ | rfl | rfl
  · left; use -y', -x'; simp_all
  simp; simp



/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    · simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . simp at hb
  simpa only [Set.mem_image, exists_exists_and_eq_and, bot_lt_coe, and_true] -- Nonempty: exists y, y ∈ E, y > ⊥


/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]
  constructor
  . intro h a ha; specialize h (-a) (by simp [ha]); grind [neg_le_neg_iff]
  grind [EReal.le_neg_of_le_neg]

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]; simp;
  refine IsLUB.csSup_eq ?_ ?_
  · apply isLUB_iff_le_iff.mpr; intro b; simp [upperBounds]
    constructor <;> intro h
    · intro a; apply le_trans ?_ h; simp; norm_cast; linarith
    specialize h 0; simpa using h
  use -1; simp; use 0; simp

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]; simp

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

#check sInf_le

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  rw [EReal.inf_eq_neg_sup]; unfold Example_6_2_8; rw [neg_eq_iff_eq_neg]; norm_cast
  refine IsLUB.csSup_eq ?_ ?_
  · apply isLUB_iff_le_iff.mpr; intro b; simp [upperBounds]
    constructor <;> intro h
    · intro a n han; rw [neg_eq_iff_eq_neg] at han; norm_cast at han; rw [han]; simp;
      apply le_trans ?_ h; norm_cast; norm_num;
      rw [show (1/10:ℝ) = 10^(-1:ℤ) by norm_num]; gcongr; norm_num; simp
    apply h (a := (-0.9:ℝ)) 0 (by simp; norm_cast; norm_num);
  use (-0.9:ℝ); simp; use 0; simp; norm_cast; norm_num


#check sSup_le

example : sSup Example_6_2_8 = 1 := by
  unfold Example_6_2_8;
  refine IsLUB.csSup_eq ?_ ?_
  · constructor <;> simp [upperBounds,lowerBounds]
    · intro a; norm_cast; simp; positivity
    intro a h; contrapose! h;
    rcases EReal.def a with ha | rfl | rfl; swap; simp at h; swap; use 0; norm_cast
    · choose b hb using ha; subst hb
      choose n hn using exists_nat_gt (1/(1-b))
      replace hn: 1/(1-b) < n+1 := by linarith
      use n; norm_cast; suffices 10^(-(n+1:ℤ)) < 1 - b by rw [Int.neg_add, Int.add_neg_one] at this; linarith
      calc
        _ ≤ 1/(n+1:ℝ) := by rw [← le_one_div (by positivity) (by positivity), one_div, zpow_neg]; simp; exact_mod_cast Chapter5.ten_pow_geq (n+1)
        _ < 1 - b := by simp_all; refine inv_lt_of_inv_lt₀ (by norm_cast at h; linarith) hn;
  use (0.9:ℝ); simp; use 0; simp; norm_cast; norm_num




/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

example : sInf Example_6_2_9 = 1 := by
  rw [EReal.inf_eq_neg_sup]; unfold Example_6_2_9; rw [neg_eq_iff_eq_neg]; norm_cast
  apply le_antisymm
  · apply sSup_le; intro b hb; simp at hb; choose n hb using hb;
    rw [neg_eq_iff_eq_neg] at hb; subst hb
    by_contra! h; have : (-1:ℝ) < - (n+1:ℝ) := by simp at *; norm_cast at *
    linarith
  apply le_sSup; simp; use 0; simp

example : sSup Example_6_2_9 = ⊤ := by
  unfold Example_6_2_9; rw [sSup_eq_top]; intro b hb;
  by_cases htop: b = ⊤; simp_all; by_cases hbot: b = ⊥;
  · subst hbot; use 1; constructor; simp; use 0; simp; norm_cast
  lift b to ℝ using (by simp_all); choose n hn using exists_nat_gt b
  use n+1; norm_cast; constructor;
  simp; use n; push_cast; linarith

example : sInf (∅ : Set EReal) = ⊤ := by
  rw [EReal.inf_eq_neg_sup]; rw [Set.neg_empty, sup_of_empty,neg_bot];

/-
Proof outline of le_sSup (and similar statements) I'm not actually gonna implement:
- x ∈ E, so E is nonempty.
  If bddAbove E, then sSup E =LUB E, sSup E = LUB E ≥ x. If not bddAbove E, then sSup E = ⊤, so sSup E = ⊤ ≥ x.
-/

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor <;> intro h
  · contrapose! h; choose x hx using h; apply le_trans (sInf_le hx) (le_sSup hx)
  subst h; simp

#check sup_of_bounded_nonempty
#check EReal.sup_of_unbounded_nonempty


/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := by
  by_cases hbot: x = ⊥; subst hbot; simp
  wlog hE: ⊥ ∉ E
  · convert this (E \ {⊥}) (by grind) hbot (by simp) using 1
    exact sup_of_neg_infty_mem
  by_cases htop: sSup E = ⊤; rw [htop]; simp
  have htop': ⊤ ∉ E := by contrapose! htop; apply sup_of_infty_mem htop
  -- It definitely seems in the spirit of the textbook to separate out the Real case
  lift E to Set ℝ using (by grind); lift x to ℝ using (by grind); simp at hx
  have hnon : E.Nonempty := by use x
  have hbdd : BddAbove E := by contrapose! htop; apply sup_of_unbounded_nonempty htop hnon
  rw [sup_of_bounded_nonempty hbdd hnon]
  -- Not sure what machinery I'm *supposed* to use for the Real case (since we're not in Ch5), but this works
  rw [EReal.coe_le_coe_iff]; apply le_csSup hbdd hx; -- Equivalent to nonempty+BddAbove req from Ch5 for LUB


/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : sInf E ≤ x := by
  rw [EReal.inf_eq_neg_sup]; rw [← Set.neg_mem_neg] at hx; have := EReal.mem_le_sup (-E) hx
  rwa [EReal.neg_le] at this

#check EReal.sup_of_unbounded_nonempty
#check EReal.sup_of_bounded_nonempty
/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := by
  wlog hE: ⊥ ∉ E
  · convert this (E \ {⊥}) (M := M) (by simp [mem_upperBounds] at *; grind) (by grind) using 1
    exact sup_of_neg_infty_mem
  rw [mem_upperBounds] at hM;
  by_cases htop: M = ⊤; subst htop; simp
  have htop': ⊤ ∉ E := by contrapose! htop; specialize hM _ htop; contrapose hM; simp_all
  by_cases hbot: sSup E = ⊥ ; rw [hbot]; simp
  have hnonempty: E.Nonempty := by contrapose! hbot; subst hbot; simp


  lift E to Set ℝ using (by grind); have ⟨x, hx⟩ := hnonempty; lift x to ℝ using (by grind); simp at hx
  have hbot' : M ≠ ⊥ := by simp_all; specialize hM x hx; rintro rfl; simp_all
  lift M to ℝ using (by simp_all); simp at hM;

  have hbdd : BddAbove E := ⟨M, hM⟩; simp at hnonempty -- Real domain: sSup is le any upper bound
  rw [sup_of_bounded_nonempty hbdd hnonempty]; simp; apply csSup_le hnonempty; apply hM




/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_upper (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M := by
  rw [EReal.inf_eq_neg_sup]; simp; rw [← EReal.le_neg]; rw[ ← Set.neg_mem_neg] at hM;
  apply sup_le_upper; convert hM using 1; ext i; simp; rw [mem_lowerBounds, mem_upperBounds];
  constructor <;> intro h <;> intro x hx
  · specialize h (-x) (by simp [hx]); rwa [EReal.neg_le]
  specialize h (-x) (by simpa using hx); rwa [ neg_le_neg_iff] at h

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib extended reals.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by sorry

theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by sorry

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal where
  toFun := toEReal
  invFun := sorry
  left_inv x := by
    sorry
  right_inv x := by
    sorry
