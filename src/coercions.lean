import tactic
import data.set.intervals -- just `data.set` for the MWE

open set

section coercions

variables (α β: Type*) (y : set β) (z : set (set β))

example (b : α) : y = ⋃ j : α, y := by { ext, simp, tauto }

-- Simplified version of the problem below
example (hy : y ∈ z) : ∃ (f : ℕ → z), (⋃ (n : ℕ), (f n).val) = y :=
-- Without the `hy :`, it means `(y : _) (H : y ∈ z)`
begin
  simp,
  existsi (λn : ℕ, (⟨y,hy⟩:z)), -- giving info to lift `y` to `z`
  exact Union_const y,
end

-- Overly simplified version that works, no coercions are needed
example : ∃ (f : ℕ → set β), (⋃ (n : ℕ), (f n)) = y :=
begin
  simp,
  existsi (λn : ℕ, y),
  ext, simp
end

end coercions

section intervals

variables (α β: Type*) [linear_order α] (a : α) (z : set α)
variables (x : α → set (set β)) (y : set β)

#check Iio a
#check ⋃ j : Iio a, x j.
#check y ∈ ⋃ j : Iio a, x j
#check y ∈ ⋃ j < a, x j

-- #help options -- useful!

-- set_option trace.debug.simplify.try_congruence true
-- set_option elaborator.coercions true
set_option trace.simplify.rewrite true

example (b : α) (hba : b < a) : z = ⋃ j : Iio a, z :=
begin
  ext y, simp, intro h,
  use b,
  exact hba,
end

example : (⋃ j : Iio a, x j) = (⋃ j : Iio a, x j.1) := by simp -- `.1` is `.val` in this context
example : (⋃ j < a, x j) = (⋃ j : Iio a, x j.1) := by simp -- same as above.

-- The original problem, now solved
example (hy: y ∈ ⋃ j : Iio a, x j) : ∃ (f : ℕ → ⋃ j : Iio a, x j), (⋃ (n : ℕ), (f n).val) = y :=
begin
  existsi (λn : ℕ, (⟨y,hy⟩: ⋃ j : Iio a, x j)),
  exact Union_const y
end

end intervals
