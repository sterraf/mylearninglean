import data.nat.prime
import data.real.basic

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

