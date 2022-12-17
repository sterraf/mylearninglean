import set_theory.cardinal.ordinal

namespace cardinal

/--
The converse of the following lemma is false (take, for instance `i = ω+1` and `κ = ℵ₀`).
-/
lemma card_le_of_le_ord {κ : cardinal} {i : ordinal} (hi : i ≤ κ.ord) :
  i.card ≤ κ :=
by { rw ← card_ord κ, exact ordinal.card_le_card hi}

/-
-- We might add this notation later

/-- `ℵ₁` is the second infinite cardinal. -/
noncomputable def aleph_1 : cardinal.{u} := aleph 1

localized "notation (name := cardinal.aleph_1) `ℵ₁` := cardinal.aleph_1" in cardinal
-/

end cardinal

open set

namespace cardinal

/-!
### Cardinal operations with ordinal indices

Results on cardinality of ordinal-indexed families of sets.
-/

open_locale cardinal

/--
Bounding the cardinal of an ordinal-indexed union of sets. 
-/
lemma mk_Union_ordinal_le_of_le {β : Type* } {κ : cardinal} {i : ordinal}
  (hi : i ≤ κ.ord) (hκ : ℵ₀ ≤ κ) (A : ordinal → set β)
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
  { have : ∀ (x : ↥(Iio i)), (λ y, A (i.enum_iso_out.inv_fun y)) (i.enum_iso_out.to_equiv.to_fun x) = A ↑x,
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
