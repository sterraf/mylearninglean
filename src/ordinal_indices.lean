import set_theory.cardinal.cofinality

universe u

namespace cardinal

/-- `ℵ₁` is the second infinite cardinal. -/
noncomputable def aleph_1 : cardinal.{u} := aleph 1

localized "notation (name := cardinal.aleph_1) `ℵ₁` := cardinal.aleph_1" in cardinal

end cardinal

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
theorem card_omega_1 : card ω₁ = ℵ₁ := card_ord _

lemma omega_lt_omega_1 :
  ω < ω₁ :=
begin
  have := (ord_lt_ord.mpr (aleph_0_lt_aleph_one)),
  rw ord_aleph_0 at this,
  exact this
end

lemma sup_sequence_lt_omega_1 (o : ℕ → ordinal.{u}) (ho : ∀ n, o n < ω₁):
  sup o < ω₁ :=
begin
  apply sup_lt_ord_lift _ ho,
  simp only [mk_denumerable,lift_aleph_0],
  unfold omega_1,
  rw [cardinal.is_regular_aleph_one.cof_eq],
  exact aleph_0_lt_aleph_one,
end

lemma is_limit_omega_1 : omega_1.is_limit := ord_is_limit (aleph_0_le_aleph 1)

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

open set

namespace cardinal

/-!
### Cardinal operations ranging over ordinals

Results on cardinality of ordinal-indexed families of sets.
-/

open_locale cardinal

/--
The converse of the following lemma is false (take, for instance `i = ω+1` and `κ = ℵ₀`).
-/
lemma card_le_of_le_ord {κ : cardinal} {i : ordinal} (hi : i ≤ κ.ord) :
  i.card ≤ κ :=
by { rw ← card_ord κ, exact ordinal.card_le_card hi}

/--
Bounding the cardinal of an ordinal-indexed union of sets. 
-/
lemma mk_Union_le_of_le {β : Type u} {κ : cardinal} {i : ordinal}
  (hi : i ≤ κ.ord) (hκ : ℵ₀ ≤ κ) (A : ordinal.{u} → set β)
  (hA : ∀ j < i, #↥(A j) ≤ κ) :
  #(↥⋃ j < i, A j) ≤ κ :=
begin
  have : #(↥⋃ j < i, A j) = #(↥⋃ (j : Iio i), A j),
  { have : (⋃ j < i, A j) = (⋃ (j : Iio i), A j) := by simp,
    rw this },
  rw this, clear this,
  rw Union_congr_of_surjective i.enum_iso_out.to_fun
    i.enum_iso_out.to_equiv.surjective,
  rotate,
  { have : ∀ (x : ↥(Iio.{u+1} i)), (λ y, A (i.enum_iso_out.inv_fun y)) (i.enum_iso_out.to_equiv.to_fun x) = A ↑x,
    { intro x, simp_rw (i.enum_iso_out.to_equiv.left_inv x) },
    exact this },
  calc
  # (↥⋃ (y : i.out.α), A ↑(i.enum_iso_out.to_equiv.inv_fun y)) ≤ 
    # i.out.α * ⨆ j : i.out.α, # ↥(A ↑(i.enum_iso_out.to_equiv.inv_fun j)) : 
    mk_Union_le _
  ... = i.card * ⨆ j : i.out.α, # ↥(A ↑(i.enum_iso_out.to_equiv.inv_fun j)) :
    by { rw mk_ordinal_out }
  ... ≤ κ * ⨆ j : i.out.α, # ↥(A ↑(i.enum_iso_out.to_equiv.inv_fun j)) : 
    mul_le_mul (card_le_of_le_ord hi) (le_refl _) (zero_le _) (zero_le κ)
  ... ≤ κ * κ : by 
    { apply mul_le_mul (le_refl κ) _ (zero_le _) (zero_le κ),
      rw ← lift_id (supr _), 
      apply lift_supr_le,
      { use κ,
      rintro x ⟨w, rfl⟩,
      refine hA _ _,
      exact (i.enum_iso_out.to_equiv.inv_fun w).property },
      intro j,
      rw lift_id,
      apply hA, 
      exact (i.enum_iso_out.to_equiv.inv_fun j).property }
  ... = κ : mul_eq_self hκ
end

/-
-- TODO:
lemma mk_Union_lt_of_lt_cof {β : Type u} (κ : cardinal.{u}) (i : ordinal.{u})
  (hi : i < κ.ord.cof.ord) (A : ordinal → set β) (hκ : ∀ j < i, #↥(A j) < κ) :
  #(↥⋃ j < i, A j) < κ :=
-/

end cardinal
