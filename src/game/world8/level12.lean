import game.world8.level11 -- hide
namespace mynat -- hide

/-

# Advanced Addition World

## Level 12: `add_one_eq_succ`

We have

  * `succ_eq_add_one (n : mynat) : succ n = n + 1`

but sometimes the other way is also convenient.
-/

/- Theorem
For any natural number $d$, we have
$$ d+1 = \operatorname{succ}(d). $$
-/
theorem add_one_eq_succ (d : mynat) : d + 1 = succ d :=
begin [nat_num_game]
--  rw succ_eq_add_one,
--  refl,

cases d with b,
rw zero_add,
apply one_eq_succ_zero,
symmetry,
apply succ_eq_add_one,


end

end mynat -- hide
