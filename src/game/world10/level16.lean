import game.world10.level15 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 16: equivalence of two definitions of `<`

Now let's go the other way. 
-/

/- Lemma : 
For all naturals $a$ and $b$,
$$
\operatorname{succ}(a)\le b
\implies
a\le b\land\lnot(b\le a).$$
-/
lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
begin [nat_num_game]
  intro h,
  split,
  have h2:= le_succ (succ a) b h,
  apply le_of_succ_le_succ,
  exact h2,
  intro g,
  apply not_succ_le_self a,
  have h2 := le_trans (succ a) b a,
  apply h2(h) g,
  --alternative proof:
  --have h2:= le_succ (succ a) b h,
  --cases g with c gc,
  --cases h with d hd,
  --rw gc at hd,
  --rw succ_eq_add_one at hd,
  --simp at hd,
  --symmetry at hd,
  --have f:= eq_zero_of_add_right_eq_self hd,
  --rw ← add_assoc at f,
  --rw add_one_eq_succ at f,
  --apply succ_ne_zero (c+d),
  --exact f,


end

/-
Now for the payoff.
-/
end mynat -- hide
