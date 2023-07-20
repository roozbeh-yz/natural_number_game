import game.world10.level3 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 4: `zero_le`

Another easy one. 
-/

/- Lemma
For all naturals $a$, $0\leq a$.
-/
lemma zero_le (a : mynat) : 0 ≤ a :=
begin [nat_num_game]
  cases a with d,
  use 0,
  refl,
  apply le_succ,
  use d,
  simp,


end

end mynat -- hide
