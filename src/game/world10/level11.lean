import game.world10.level10 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 11: `add_le_add_right`

If you're faced with a goal of the form `forall t, ...`, then the next
line is "so let $t$ be arbitrary". The way to do this in Lean is `intro t`.
-/

/- Lemma
For all naturals $a$ and $b$, $a\le b$ implies that for all naturals $t$,
$a+t\le b+t$.
-/
theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin [nat_num_game]
  intro f,
  intro t,
  induction b with d,
  rw le_zero _ f,
  use 0,
  refl,
  cases f with c fc,
  use c,
  rw fc,
  simp,

  
end

end mynat -- hide
