/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Violeta Hernández Palacios, Pedro Sánchez Terraf
-/
import borel_hierarchy

/-!
# Cardinal of sigma-algebras

If a sigma-algebra is generated by a set of sets `s`, then the cardinality of the sigma-algebra is
bounded by `(max (#s) 2) ^ ℵ₀`.
This is stated in `measurable_space.cardinal_generate_measurable_le`
and `measurable_space.cardinal_measurable_set_le`.

In particular, if `#s ≤ 𝔠`, then the generated sigma-algebra has cardinality at most `𝔠`, see
`measurable_space.cardinal_measurable_set_le_continuum`.

For the proof, we rely on the explicit inductive construction of the sigma-algebra generated by
`s` provided by `pointclasses.gen_measurable`
(instead of the inductive predicate `generate_measurable`).
-/

universe u
variables {α : Type u}

namespace measurable_space

open_locale cardinal ordinal
open cardinal set pointclasses

/-- At each step of the inductive construction, the cardinality bound `≤ (max (#s) 2) ^ ℵ₀` holds.

The result holds for arbitrary `i`, but it is easier to prove this way -/
lemma cardinal_sigma0_le (s : set (set α)) (i : ordinal.{u}) (hi : i ≤ ω₁) :
  #(sigma0 s i) ≤ (max (#s) 2) ^ aleph_0.{u} :=
begin
  induction i using ordinal.induction with i IH,
  have Upi0sub : (⋃ j < i, pi0 s j) ⊆ s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j,
  { simp only [mem_singleton_iff, union_insert, union_singleton, mem_insert_iff, Union_subset_iff],
    intros j hj x hx,
    rcases classical.em (j=0) with rfl | hjnz,
    { simp only [mem_singleton_iff, union_insert, union_singleton, mem_insert_iff, pi0_zero] at hx,
      exact mem_union_left _ hx },
    { rw pi0_eq_compl_sigma0 s j hjnz at hx,
      exact mem_union_right _ (mem_Union.mpr ⟨j, mem_Union.mpr ⟨hj, hx⟩⟩) } },
  have cardcompl : ∀ j, #(sigma0 s j) = #(compl '' sigma0 s j) :=
    λ j, cardinal.eq.mpr (⟨equiv.set.image _ _  compl_injective⟩),
  have A := aleph_0_le_aleph 1,
  have B : aleph 1 ≤ (max (#s) 2) ^ aleph_0.{u} :=
    aleph_one_le_continuum.trans (power_le_power_right (le_max_right _ _)),
  have C : ℵ₀ ≤ (max (#s) 2) ^ aleph_0.{u} := A.trans B,
  have L : #(↥(s ∪ {∅, univ})) ≤ (max (#s) 2) ^ aleph_0.{u},
  { apply_rules [(mk_union_le _ _).trans, add_le_of_le C, mk_image_le.trans],
    { exact (le_max_left _ _).trans (self_le_power _ one_lt_aleph_0.le) },
    repeat { simp only [mk_fintype, fintype.card_unique, nat.cast_one, mk_singleton],
      exact one_lt_aleph_0.le.trans C } },
  have K : #(↥⋃ j < i, compl '' sigma0 s j) ≤ (max (#s) 2) ^ aleph_0.{u},
  { apply mk_Union_ordinal_le_of_le (hi.trans $ ord_le_ord.mpr B) C,
    intros j hj,
    rw ← cardcompl,
    exact IH j hj (le_of_lt $ lt_of_lt_of_le hj hi) },
  have J : #(↥(s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j)) ≤ (max (#s) 2) ^ aleph_0.{u},
    { calc
      #(↥(s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j)) ≤
        #(↥(s ∪ {∅, univ})) + #(↥⋃ j < i, compl '' sigma0 s j) : mk_union_le _ _
      ... ≤ (max (#s) 2) ^ aleph_0.{u} + (max (#s) 2) ^ aleph_0.{u} :
        (add_le_add (le_refl _) K).trans (add_le_add L (le_refl _))
      ... = (max (#s) 2) ^ aleph_0.{u} :
        (add_eq_max C).trans (max_eq_right (le_refl _)) },
  -- The main calculation:
  calc
  #↥(sigma0 s i) =
    #↥(range (λ (f : ℕ → (↥⋃ j < i, pi0 s j)), ⋃ n, ↑(f n))) :
    by { rw sigma0_eq_Union_pi0, simp }
  ... ≤ #(ℕ → (↥⋃ j < i, pi0 s j))                  : mk_range_le
  ... = prod (λ n : ℕ, #(↥⋃ j < i, pi0 s j))        : mk_pi _
  ... = #(↥⋃ j < i, pi0 s j) ^ aleph_0.{u}          : by { simp [prod_const] }
  ... ≤ #(↥(s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j)) ^ aleph_0.{u} :
    power_le_power_right (mk_le_mk_of_subset Upi0sub)
  ... ≤ (max (# ↥s) 2 ^ aleph_0.{u}) ^ aleph_0.{u}  : power_le_power_right J
  ... ≤ (max (# ↥s) 2 ^ aleph_0.{u})                :
    by { rwa [← power_mul, aleph_0_mul_aleph_0] }
end

theorem cardinal_gen_measurable_le (s : set (set α)) :
  #(gen_measurable s) ≤ (max (#s) 2) ^ aleph_0.{u} := cardinal_sigma0_le _ _ (le_refl _)

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma-algebra has cardinality at
most `(max (#s) 2) ^ ℵ₀`. -/
theorem cardinal_generate_measurable_le (s : set (set α)) :
  #{t | generate_measurable s t} ≤ (max (#s) 2) ^ aleph_0.{u} :=
begin
  rw generate_measurable_eq_gen_measurable,
  exact cardinal_gen_measurable_le s,
end

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma
algebra has cardinality at most `(max (#s) 2) ^ ℵ₀`. -/
theorem cardinal_measurable_set_le' (s : set (set α)) :
  #{t | @measurable_set α (generate_from s) t} ≤ (max (#s) 2) ^ aleph_0.{u} :=
cardinal_generate_measurable_le s

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_generate_measurable_le_continuum {s : set (set α)} (hs : #s ≤ 𝔠) :
  #{t | generate_measurable s t} ≤ 𝔠 :=
(cardinal_generate_measurable_le s).trans begin
  rw ←continuum_power_aleph_0,
  exact_mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le)
end

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_measurable_set_le_continuum {s : set (set α)} :
  #s ≤ 𝔠 → #{t | @measurable_set α (generate_from s) t} ≤ 𝔠 :=
cardinal_generate_measurable_le_continuum

end measurable_space
