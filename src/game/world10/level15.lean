--import mynat.lt -- definition of <
import game.world10.level14 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 15: introducing `<`

To get the remaining collectibles in this world, we need to
give a definition of `<`. By default, the definition of `a < b`
in Lean, once `≤` is defined, is this:

`a < b := a ≤ b ∧ ¬ (b ≤ a)`

. But a much more usable definition would be this:

`a < b := succ(a) ≤ b`

. Let's prove that these two definitions are the same
-/

/- Lemma : 
For all naturals $a$ and $b$,
$$a\le b\land\lnot(b\le a)\implies\operatorname{succ}(a)\le b.$$
-/
lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=
begin [nat_num_game]
  intro h,
  cases h with h1 h2,
  cases h1 with c h1c,
  cases c with d,
  exfalso,
  apply h2,
  rw h1c,
  refl,
  rw h1c,
  rw add_succ,
  apply succ_le_succ,
  use d,
  refl,

end

end mynat -- hide
