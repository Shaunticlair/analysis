import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp] -- Cauchy sequences are still equivalent to their underlying sequences
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

-- We can turn Cauchy sequences into functions ℕ → ℚ
instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where -- To sequence, then grab .seq
  coe a n := a.toSequence (n:ℤ)

#check Sequence.eval_coe_at_int
@[simp] -- Casting to a function agrees with toSequence
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp] -- Coercing function → cauchy → function gives original function (fun → cauchy → sequence → .seq (fun) )
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
    intro e he;
    specialize hab (e/2) (by linarith); specialize hbc (e/2) (by linarith);
    rw [Rat.eventuallyClose_iff] at *;
    choose N hab using hab; choose M hbc using hbc; use N+M
    intro n hn
    specialize hab n (by linarith); specialize hbc n (by linarith)
    have h1 := abs_sub_le (a n) (b n) (c n)
    linarith

theorem Sequence.equiv_refl (a:ℕ → ℚ) : Equiv a a := by
  rw [equiv_iff]; intro ε hε; use 0; intro n hn; simp; linarith

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := by intro x; apply Sequence.equiv_refl
     symm := Sequence.equiv_symm
     trans := Sequence.equiv_trans
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  intro e he; refine ⟨0, by simp_all, ?_⟩; intro n hn m hm; simp_all
  rw [Rat.Close]; simp; linarith

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  choose A hApos hA using (isBounded_of_isCauchy ha)
  choose B hBpos hB using (isBounded_of_isCauchy hb)
  rw [IsCauchy.coe] at *
  intro ε hε
  have : (A+B+1) > 0 := by linarith
  choose N1 ha using ha ((ε /2) / (A+B+1)) (by apply div_pos (half_pos hε) (by linarith))
  choose N2 hb using hb ((ε /2) / (A+B+1)) (by apply div_pos (half_pos hε) (by linarith))

  use max N1 N2
  intro j hj k hk
  specialize ha j ?_ k ?_  <;> try omega
  specialize hb j ?_ k ?_ <;> try omega
  rw [ ←Rat.Close] at *
  have h1 := Section_4_3.close_mul_mul' ha hb
  convert Section_4_3.close_mono h1 ?_
  specialize hA k; simp at hA;
  specialize hB j; simp at hB;
  rw [show ε = (ε /2) + (ε /2) by ring]
  gcongr
  · field_simp; rw [div_le_div_iff₀] <;> try positivity
    suffices |b j| ≤  (A + B + 1)  by nlinarith
    linarith [hB]
  · field_simp; rw [div_le_div_iff₀] <;> try positivity
    suffices |a k| ≤  (A + B + 1)  by nlinarith
    linarith [hA]

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  rw [equiv_def] at *
  intro ε hε;
  choose B hBpos hB using (isBounded_of_isCauchy hb)

  specialize haa' (ε / (B+1)) (by apply div_pos hε (by linarith))
  rw [Rat.eventuallyClose_def] at *
  choose A haa' using haa';
  simp [Rat.closeSeq_def] at *
  use A
  peel 5 haa' with n hn hN _ _ haa'
  specialize hB n; simp at hB;
  simp [hn, hN] at *

  apply Section_4_3.close_mul_right (z:= b n.toNat) at haa'
  apply Section_4_3.close_mono haa'
  calc
    _ = ε / (B + 1) * (B + 1) := by field_simp
    _ ≥ ε / (B + 1) * |b n.toNat| := by gcongr; linarith

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  constructor <;> intro h
  · repeat rw [Real.ratCast_def] at h
    rw [LIM_eq_LIM, Sequence.equiv_iff] at h
    contrapose! h
    wlog h': q > r
    · push_neg at h'; have hqr: q < r := lt_of_le_of_ne h' h
      choose e he habs using this r q h.symm hqr
      rw [abs_sub_comm] at habs; use e, he
    use |q-r|/2; have : q - r > 0 := by linarith;
    refine ⟨by rw [abs_of_pos this]; linarith, ?_⟩
    intro n; use n; simp; push_neg; linarith
    apply Sequence.IsCauchy.const
    apply Sequence.IsCauchy.const
  · rw [h]

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

theorem Real.natCast_def (n:ℕ) : (n:Real) = LIM (fun _ ↦ n) := by rw [LIM_def]; rfl

theorem Real.OfNat_def (n:ℕ) : OfNat.ofNat n = LIM (fun _ ↦ n) := by rw [LIM_def]; rfl

lemma Real.NatCast_eq_ratCast (n:ℕ) : n = ((n:ℚ):Real) := rfl

lemma Real.OfNat_eq_ratCast (n:ℕ) : OfNat.ofNat n = ((n:ℚ):Real) := rfl

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

@[simp]
theorem Real.LIM.one : LIM (fun _ ↦ (1:ℚ)) = 1 := by rw [←ratCast_def 1]; rfl


instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

theorem Real.intCast_def (n:ℤ) : (n:Real) = LIM (fun _ ↦ n) := by rw [LIM_def]; rfl

lemma Real.IntCast_eq_ratCast (n:ℤ) : n = ((n:ℚ):Real) := rfl


/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  rw [Real.ratCast_def, Real.ratCast_def, Real.ratCast_def]
  apply Real.LIM_add
  <;> apply Sequence.IsCauchy.const


/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  rw [Real.ratCast_def, Real.ratCast_def, Real.ratCast_def]
  apply Real.LIM_mul
  <;> apply Sequence.IsCauchy.const

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

lemma Real.neg_one_mul (x:Real) : ((-1:ℚ):Real) * x = -x := by rfl

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  simp [← neg_one_mul, Real.ratCast_mul]

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  rw [← neg_one_mul, Real.ratCast_def, Real.LIM_mul];
  congr; ext n; simp
  apply Sequence.IsCauchy.const
  exact ha

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  peel 8 ha with e he N hN i hi j hj ha
  simp_all; simp [le_trans hN hi, le_trans hN hj] at *
  rw [Rat.Close] at *; rw [abs_sub_comm]; simp;
  convert ha using 2; ring


/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
AddGroup.ofLeftAxioms
(by
  intro a b c
  choose x hx using eq_lim a
  choose y hy using eq_lim b
  choose z hz using eq_lim c
  rw [hx.2, hy.2, hz.2]
  repeat rw [Real.LIM_add]
  congr 1; ring
  on_goal 2 => apply Sequence.IsCauchy.add
  on_goal 6 => apply Sequence.IsCauchy.add
  any_goals exact hx.1
  any_goals exact hy.1
  any_goals exact hz.1
)
(by
  intro a
  choose x hx using eq_lim a
  rw [hx.2, ← Real.LIM.zero, Real.LIM_add]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.const
  exact hx.1
)
(by
  intro a
  choose x hx using eq_lim a
  rw [hx.2, ← Real.LIM.zero, Real.neg_LIM, Real.LIM_add]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.neg
  all_goals exact hx.1)

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
  rw [show a-b = a + (-b) by ring]
  apply Sequence.IsCauchy.add
  exact ha; exact Sequence.IsCauchy.neg _ hb

/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  rw [Real.sub_eq_add_neg, Real.neg_LIM, Real.LIM_add ]
  congr; ring
  on_goal 2 => apply Sequence.IsCauchy.neg
  any_goals exact ha
  any_goals exact hb

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  rw [Real.sub_eq_add_neg, Real.neg_ratCast, Real.ratCast_add]
  congr; ring

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    choose x hx using eq_lim a
    choose y hy using eq_lim b
    rw [hx.2, hy.2]
    rw [Real.LIM_add, Real.LIM_add]
    congr 1; ring
    any_goals apply hx.1
    any_goals apply hy.1

lemma Real.mul_comm' (a b:Real) : a * b = b * a := by
  choose x hx using eq_lim a
  choose y hy using eq_lim b
  rw [hx.2, hy.2]
  rw [Real.LIM_mul, Real.LIM_mul]
  congr 1; ring
  any_goals apply hx.1
  any_goals apply hy.1

lemma Real.one_mul' (a:Real) : (1:Real) * a = a := by
  choose x hx using eq_lim a
  rw [hx.2,← Real.LIM.one, Real.LIM_mul]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.const
  exact hx.1

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := Real.mul_comm'
  mul_assoc := by
    intro a b c
    choose x hx using eq_lim a
    choose y hy using eq_lim b
    choose z hz using eq_lim c
    rw [hx.2, hy.2, hz.2]
    rw [Real.LIM_mul, Real.LIM_mul, Real.LIM_mul, Real.LIM_mul]
    congr 1; ring
    on_goal 2 => apply Sequence.IsCauchy.mul
    on_goal 6 => apply Sequence.IsCauchy.mul
    any_goals apply hx.1
    any_goals apply hy.1
    any_goals apply hz.1
  one_mul := Real.one_mul'
  mul_one := by intro x; rw [mul_comm']; apply Real.one_mul'

lemma Real.left_distrib' (a b c:Real) : a * (b + c) = a * b + a * c := by
  choose x hx using eq_lim a
  choose y hy using eq_lim b
  choose z hz using eq_lim c
  rw [hx.2, hy.2, hz.2]
  rw [Real.LIM_mul, Real.LIM_add, Real.LIM_mul, Real.LIM_mul, Real.LIM_add]
  congr 1; ring
  on_goal 1 => apply Sequence.IsCauchy.mul
  on_goal 3 => apply Sequence.IsCauchy.mul
  on_goal 8 => apply Sequence.IsCauchy.add
  any_goals apply hx.1
  any_goals apply hy.1
  any_goals apply hz.1

lemma Real.zero_mul' (a:Real) : (0:Real) * a = 0 := by
  obtain ⟨x, hx, rfl⟩ := eq_lim a
  rw [← Real.LIM.zero, Real.LIM_mul]
  congr 1; ext n; simp
  apply Sequence.IsCauchy.const
  exact hx

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := Real.left_distrib'
  right_distrib := by
    intro a b c
    rw [mul_comm, Real.left_distrib', mul_comm c a, mul_comm c b]
  zero_mul := Real.zero_mul'
  mul_zero := by intro a; rw [mul_comm']; apply Real.zero_mul'
  mul_assoc := mul_assoc
  natCast_succ := by
    intro n;
    have hn:= NatCast_eq_ratCast n
    have h1 := Real.OfNat_eq_ratCast 1
    simp only [Nat.cast] at * -- Fix weird slightly different casting pathways
    rw [hn, h1]
    rw [Real.ratCast_add]
    norm_cast
  intCast_negSucc := by
    intro n;
    have hn:= NatCast_eq_ratCast (n+1)
    have h1 := Real.IntCast_eq_ratCast (Int.negSucc n)
    simp only [Int.cast] at *
    rw [hn, h1]
    rw [Real.neg_ratCast] -- Move the negative into the int domain
    -- We just need to check the ints are the same
    congr 1 -- Leave it to the int machinery

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := rfl -- real 0 is constructed as ratCast 0
  map_one' := rfl
  map_add' := by intro x y; rw [Real.ratCast_add]
  map_mul' := by intro x y; rw [Real.ratCast_mul]

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  rw [bounded_away_zero_def]; push_neg; intro c hc
  -- For any c, we can go farther in the sequence to get closer than c to 0
  choose m hm using exists_nat_ge (1/c); use m
  replace hm : 1/c < m + 1 := by linarith
  rw [show ((-(m:ℤ) - 1) = -(m+1)) by ring, abs_of_nonneg]
  rw [zpow_neg, show c =(1/c)⁻¹ by field_simp] -- Remove abs
  -- Cancel out ⁻¹
  gcongr
  -- 1/c < m+1 ≤ 10^(m+1)
  apply lt_of_lt_of_le hm
  norm_cast; apply ten_pow_geq -- norm_cast to deal with how our nat is cast
  -- 0 < 10, so exponent is pos
  apply zpow_nonneg (by norm_num)

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  rw [bounded_away_zero_def]; push_neg; intro c hc
  use 0; simp [hc]


/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  rw [Sequence.isBounded_def]; push_neg; intro M hM
  rw [Sequence.boundedBy_def]; push_neg
  choose N hN using exists_nat_gt M
  have := ten_pow_geq (N+1)
  use N; simp
  apply lt_of_lt_of_le hN
  norm_cast; linarith

abbrev Real.truncated_seq (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ) : ℕ → ℚ :=
  fun k ↦ if k < n then C else a k

lemma Real.truncated_seq_equiv (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ):
  Sequence.Equiv a (Real.truncated_seq n C a) := by
  unfold Real.truncated_seq
  intro e he; use n; intro i hia _; simp at hia; simp [hia]
  simp [show 0 ≤ i by linarith, show ¬ i < n by linarith]
  rw [Rat.Close]; simp; linarith

lemma Real.truncated_seq_isCauchy (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ)
  (ha: (a:Sequence).IsCauchy) :
  (Real.truncated_seq n C a :Sequence).IsCauchy := by
  have := Real.truncated_seq_equiv n C a
  have := Sequence.isCauchy_of_equiv this
  rwa [this] at ha

lemma Real.truncated_seq_eq_LIM (n : ℕ ) (C : ℚ ) (a : ℕ → ℚ)
  (ha: (a:Sequence).IsCauchy) :
  LIM a  = LIM (Real.truncated_seq n C a) := by
  rw [LIM_eq_LIM ha (Real.truncated_seq_isCauchy n C a ha)]
  apply Real.truncated_seq_equiv n C a

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x -- x has a corresponding sequence b
  simp only [←LIM.zero, ne_eq] at hx -- x is nonzero => b not equiv 0 sequence
  -- x ≠ 0 → sequences not equivalent → they always eventually separate by some ε > 0
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  -- Grab the distance ε that b and 0 always manage to separate by
  choose ε hε hx using hx -- a "fence" that b always breaks out of
  -- At some time N, b is trapped inside a fence of ε/2 (can't get too far from itself)
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  -- b must exit the ε fence sometime n₀ after time N
  choose n₀ hn₀ hx using hx N
  -- b must stay within ε/2 distance of that time n₀ where it broke out of the ε
  -- fence, so it can only be at best ε/2 close to 0
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj; -- (b j) stays close to (b n₀)
    have := hb' j hj n₀ hn₀; rw [Section_4_3.dist] at this
    suffices ε ≤ |b j| + ε/2  by linarith
    apply le_trans (le_of_lt hx)
    suffices |b n₀| ≤ |b j| + |b j - b n₀|  by linarith
    have := Section_4_3.dist_le 0 (b j) (b n₀)
    repeat rw [Section_4_3.dist_eq] at this
    field_simp at this
    exact this

  -- Define a new sequence that removes terms that aren't guaranteed to be bounded away from 0
  -- This sequence is equivalent to our old one, so it's also cauchy
  have not_hard := Real.truncated_seq_equiv n₀ (ε/2) b
  replace not_hard := Sequence.equiv_symm not_hard
  set a := truncated_seq n₀ (ε/2) b

  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  -- We'll use a as our bounded-away sequence
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  -- Check that it's bounded away by ε/2
  -- Low sequence: exactly ε/2. High sequence: already proven.
  intro n; by_cases hn: n < n₀ <;> simp [a, truncated_seq, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
  rw [←LIM.zero, ne_eq]
  rw [LIM_eq_LIM ha_cauchy (by convert Sequence.IsCauchy.const 0)]
  choose e he ha using ha
  rw [Sequence.equiv_iff]; push_neg
  use e/2, half_pos he; intro N; use N+1, (by linarith)
  specialize ha (N+1); simp
  linarith

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

-- Since we know that our terms have a lower bound, the 1/x terms cannot blow up
-- So, we just have to scale down a1-a2 closeness sufficiently (by 1/c^2)
/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- Each term is nonzero: useful for making sure reciprocals are defined
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  -- Each term is at least c away from zero
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha

  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  -- Reciprocal Cauchy ↔ reciprocals all eventually become close
  intro ε hε;
  -- We'll get a within c² * ε closeness on the original sequence
  -- Because when we compare reciprocals, we divide by at least c²
  -- 1/x - 1/y = (y - x) / (xy) and |xy| ≥ c²
  specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  -- Select arbitrary n, m ≥ N to show closeness
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  -- Algebraic manipulation
  calc
    -- Valid reciprocals because a m, a n ≠ 0
    _ = |(a m - a n) / (a m * a n)| := by congr; field_simp [ha' m, ha' n]; grind
    -- Use c bound, then flip order
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    -- Use the bound: c^2 term cancels nicely
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]


/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  ---- Set up cauchy conditions so that we can work with sequence limits
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  -- Cancel out terms to get the desired equality
  -- We do this by moving inside the LIM, and proving the *sequences* are equal
  have claim1 : P = LIM b⁻¹ := by
    -- Can combine multiplication under LIM (terms are cauchy)
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    -- Use congr to remove LIM, then prove for any arbitrary input to sequences
    rcongr n;
    -- If a n ≠ 0, then inverse sequence behaves normally, can cancel
    simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    -- Combine multiplication under LIM *and* swap LIM a and LIM b
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    -- Now, we can cancel out the inverse the *other* way
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  simp_all

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  -- Grab a bounded-away-from-zero sequence representative of x
  -- Then, invert that sequence termwise
  -- Take the limit of the result
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

-- If we *start* with a bounded-away-from-zero sequence,
-- Then the inverse can just be defined using this sequence
-- Rather than needing to find a new one
theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0 -- From bounded away from zero, the limit can't be zero
  set x := LIM a
  -- Grab the bounded-away sequence that inv uses to define x⁻¹
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx, -Quotient.eq]
  -- Lims equivalent → inverse lims equivalent
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  choose a ha hba hla using boundedAwayZero_of_nonzero hx
  rw [hla, Real.inv_def hba ha]
  rw [Real.LIM_mul ha (Real.inv_isCauchy_of_boundedAwayZero hba ha)]
  rw [OfNat_eq_ratCast, Real.ratCast_def]
  rcongr n; simp [(nonzero_of_boundedAwayZero hba n)]

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm]; apply Real.self_mul_inv hx

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by use (0:ℚ), (1:ℚ); simp; -- Use injectivity of ratCast, rats are distinct
  mul_inv_cancel := by intro a ha; apply Real.self_mul_inv ha
  inv_zero := Real.inv_zero
  ratCast_def := by
    intro q;
    observe hden: q.den ≠ 0
    observe hq : q = q.num / q.den
    nth_rw 1 [hq]; -- We want to show that ratCast passes through div
    rw [div_eq, div_eq_mul_inv, ← Real.ratCast_mul]; -- Div = invmul, ratCast mul
    congr
    -- Move inv inside cast and LIM
    rw [ratCast_def, natCast_def ]
    rw [inv_def (BoundedAwayZero.const ?_) (Sequence.IsCauchy.const _)]
    -- Clean up
    congr
    norm_cast


  qsmul := _
  nnqsmul := _

-- Cancellation law
theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  observe: x * z * z⁻¹ = y * z * z⁻¹
  --field_simp at this; exact this
  have : x * (z * z⁻¹) = y * (z * z⁻¹) := by rw [← mul_assoc, ← mul_assoc, this]
  rw [Real.self_mul_inv hz, mul_one, mul_one] at this; exact this

-- ONLY works if we know z = 0
theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  push_neg; use 0, 1, 0; simp


/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by
    rw [Sequence.equiv_def] at hab
    specialize hab 1 (by norm_num)
    rw [Sequence.isBounded_of_eventuallyClose hab] at ha
    exact ha

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [Real.OfNat_def, show ((0:ℕ):ℚ) = 0 by norm_cast]
  -- Equivalent sequences
  rw [LIM_eq_LIM (Sequence.IsCauchy.harmonic') (Sequence.IsCauchy.const 0)]
  rw [Sequence.equiv_def]; intro e he
  -- N > 1/e means that for n ≥ N, 1/(n+1) < e
  choose N hN using exists_nat_ge (1/e)
  use N+1; intro i hi _; simp at hi;
  lift i to ℕ using (by linarith)
  simp [hi, Rat.Close]
  rw [abs_of_nonneg] -- 1/(i+1) is nonneg
  -- Handle inequality chain
  observe hip: 0 < ((i:ℚ)+1)
  have hN : (N:ℚ) + 1 ≤ (i:ℚ) + 1 := by norm_cast; linarith
  have he : 1/e ≤ (i:ℚ)+1 := by linarith
  -- We just need to invert both sides
  rw [ inv_le_comm₀ (by linarith) (by linarith)];
  field_simp [he]
  apply Rat.inv_nonneg (by linarith)

end Chapter5
