import set_theory.cardinal.cofinality

universe u

namespace ordinal
open cardinal
open_locale ordinal cardinal

/--
The first uncountable ordinal in type universe `u`.
You can use the notation `ω₁`.
-/
noncomputable def omega_1 : ordinal.{u} := (aleph 1).ord

localized "notation (name := ordinal.omega_1) `ω₁` := ordinal.omega_1" in ordinal

@[simp]
theorem card_omega_1 : card ω₁ = aleph 1 := card_ord _

lemma omega_lt_omega_1 :
  ω < ω₁ :=
begin
  have := (ord_lt_ord.mpr (aleph_0_lt_aleph_one)),
  rw ord_aleph_0 at this,
  exact this
end

lemma is_limit_omega_1 : omega_1.is_limit := ord_is_limit (aleph_0_le_aleph 1)

end ordinal
-- up to this point, only `import set_theory.cardinal.ordinal` is needed.

namespace ordinal
open cardinal
open_locale ordinal cardinal

lemma sup_sequence_lt_omega_1 (o : ℕ → ordinal.{u}) (ho : ∀ n, o n < ω₁):
  sup o < ω₁ :=
begin
  apply sup_lt_ord_lift _ ho,
  simp only [mk_denumerable,lift_aleph_0],
  unfold omega_1,
  rw [cardinal.is_regular_aleph_one.cof_eq],
  exact aleph_0_lt_aleph_one,
end

/--
Denumerably many elements chosen from a nondecreasing `ω₁`-sequence of sets,
all lie in one of the sets.
-/
lemma bound_omega_1_of_increasing_of_sequence {β : Type*} {A : ordinal → set β}
  {hA : ∀ j k (hjk : j ≤ k), A j ⊆ A k} {f : ℕ → β} (hf : ∀ n, ∃ i, i < ω₁ ∧ f n ∈ A i) :
  ∃ i (hi : i < ω₁), ∀ n, f n ∈ A i :=
begin
  choose o ho using hf,
  use sup o,
  split,
  { finish [sup_sequence_lt_omega_1] },
  intro n,
  specialize ho n,
  specialize hA (o n) (sup o) (le_sup o n),
  tauto
end

end ordinal
