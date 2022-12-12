import data.nat.prime
import data.real.basic
import topology.basic -- for namespace fiddling

/-
  Some experiments based on LFTCM20
-/

namespace nat -- in place of 'open'

theorem infinitude_of_primes : ∀ N, ∃p ≥ N, prime p:=
begin
  intro N,

  let M := factorial N + 1,
  let p := min_fac M,

  have pp: prime p := 
  begin
    refine min_fac_prime _,
    refine ne_of_gt _,
    have : factorial N > 0 := factorial_pos N,
    exact succ_lt_succ this,
    /-
    otherwise "import tactic.linarith" at the beginning and
    put "linarith," here.
    -/
  end,
  
  use p,
  split,
  { by_contradiction, 
    have h₁ : p ∣ factorial N + 1:= min_fac_dvd M, -- divides is '\|' 
    have h₂ : p ∣ factorial N := 
    begin
      show_term { refine dvd_factorial _ _,
      exact prime.pos pp,
      exact le_of_not_ge h, }
    end,
    -- I can leave "by library search," below
    have h : p ∣ 1 := iff.mp (nat.dvd_add_right h₂) h₁,
    -- 'iff' in place of 'Iff'
    -- hint here: use 'library_search,' with nothing after it
    exact prime.not_dvd_one pp h, },
  { exact pp },
end

end nat

lemma mylemma: ∀x:ℕ, 0 ≤ x :=
begin
  intro,
  exact zero_le x
end

#check `[exact λ (x : ℕ), zero_le x]

open nat

example (m n: ℕ) (h : m ≤ n): (m:ℝ) ≤ n :=
begin
  exact cast_le.2 h,
end

#check cast_lt.2

lemma real_not_nat : ∃ (x : ℝ), ∀ (n : ℕ), x ≠ n :=
begin
  use -1,
  intro,
  have : (-1:ℝ) < (0:ℕ) := by norm_num,
  have : ∀ (n : ℕ), (0 : ℝ) ≤ n := cast_nonneg,
  have : ∀ (n : ℕ), (0 : ℝ) < n +1 :=
  begin
    intro m,
    exact cast_add_one_pos m
  end,
  have : ∀ (n : ℕ), (-1 : ℝ) < n :=
  begin
    intro n,
    exact neg_lt_iff_pos_add.mpr (this n)
  end,
  exact ne_of_lt (this n),
end

example (P R : Prop) (p: P) (q: ¬P) : R := absurd p q

example (P R : Prop) (p: P) (q: ¬P) : R := false.rec R (q p)

-- Playing around classically. 
lemma exists_of_nonempty {α : Type}  [nonempty α] : (∃ x : α, true) :=
begin
  by_contradiction,
  push_neg at h,
  apply nonempty.elim, 
  assumption,
  intro alp,
  apply h alp trivial,
end

-- Experimenting with namespaces and `_root_`.
namespace is_open

#check and                -- topology lemma
#check _root_.is_open.and -- same as above
#check _root_.and         -- logical `and` at the root namespace

end is_open

-- Example using `constructor`
example {α : Type*} (P Q : α → Prop) : (∀ x, P x ∧ Q x) → (∀x, P x ∨ Q x) :=
begin
  intros h x,
  constructor, -- Chooses the lhs, first constructor that matches.
  exact (h x).left
end

section including_omitting

class cls := (val : ℕ) -- From the Reference Manual, Sect. 3.2

variables (x : ℝ) [c : cls]

def ex2b : ℕ := 5

#check ex2b       -- ex2b : ℕ
#check @ex2b      -- ex2b : ℕ

include c

def ex2c : ℕ := 5

#check ex2c       -- ex2c : ℕ
#check @ex2c      -- ex2c : Π [c : cls], ℕ

example : ex2c = (5 : ℕ) := rfl -- Here the `5` is just natural

omit c
include x

def ex2d : ℕ := 5

#check ex2d       -- ex2d : ℝ → ℕ
#check @ex2d      -- ex2d : ℝ → ℕ

example : ex2d = (5 : ℕ) := rfl -- Here the `5` is coerced to `ℝ → ℕ` 

end including_omitting

example : ex2d = (5 : ℕ) := rfl -- Here too

-- Useful tracing for turning non-terminal `simp`s into `simp only`s:
set_option trace.simplify true
set_option trace.simplify.failure false
set_option trace.simplify.rewrite_failure false
-- Accompanying terminal (xD) script. End input with Ctrl-D.
/-
sed -e "s/.*\\[simplify.rewrite\\] \\[\([^[]*\)]:.*/\\1,/g" -e "s/set\\.//g" -e "s/^  .*//g" | grep -v "^$"
-/