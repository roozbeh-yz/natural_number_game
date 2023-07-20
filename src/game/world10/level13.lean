import game.world10.level12 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 13: `not_succ_le_self`

Turns out that `¬ P` is *by definition* `P → false`, so you can just
start this one with `intro h` if you like. 

## Pro tip:

```
  conv begin
    to_lhs,
    rw hc,
  end,
```

is an incantation which rewrites `hc` only on the left hand side of the goal.
Look carefully at the commas. You don't need to use `conv` to solve this,
but it's a helpful trick when `rw` is rewriting too much.
-/

/- Lemma
For all naturals $a$, $\operatorname{succ}(a)$ is not at most $a$.
-/
theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
begin [nat_num_game]
  rw succ_eq_add_one,
  intro h,
  cases h with c hc,
  simp at hc,
  symmetry at hc,
  have g:= eq_zero_of_add_right_eq_self hc,
  rw add_one_eq_succ at g,
  apply succ_ne_zero c,
  exact g,


end

end mynat -- hide

-- thanks to Filip Szczepański for this proof (nicer than the original; I was doing -- hide
-- induction a before cases h) -- hide
