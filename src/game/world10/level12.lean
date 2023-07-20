import game.world10.level11 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 12: `le_of_succ_le_succ`

-/

/- Lemma
For all naturals $a$ and $b$,
$\operatorname{succ}(a)\le\operatorname{succ}(b)\implies a\le b.$
-/
theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
begin [nat_num_game]
  intro h,
  cases h with c hc,
  use c,
  --rw succ_add at hc,
  --apply succ_inj,
  --exact hc,
  rw succ_eq_add_one at hc,
  rw succ_eq_add_one at hc,
  rw add_comm a at hc,
  rw add_assoc at hc,
  rw add_comm at hc,
  apply add_left_cancel 1 b (a+c),
  rw hc,
  refl,


end
  
end mynat -- hide
