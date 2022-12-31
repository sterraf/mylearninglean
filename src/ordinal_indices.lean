import set_theory.cardinal.ordinal
import set_theory.cardinal.cofinality

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

universes u v

/-!
### Cardinal operations with ordinal indices

Results on cardinality of ordinal-indexed families of sets.
-/

open_locale cardinal

set_option pp.universes true
-- cardinal.basic
#check cardinal.le_sum -- for universe issues only
#check cardinal.sum_add_distrib -- for universe issues only
#check cardinal.sum_add_distrib' -- for universe issues only
#check cardinal.lift_sum -- for universe issues only
#check cardinal.sum_le_sum -- for universe issues only
#check cardinal.bdd_above_range -- for universe issues only
#check cardinal.supr_le_sum -- for universe issues only
#check cardinal.sum_le_supr_lift
#check cardinal.sum_le_supr
#check cardinal.supr_of_empty -- for universe issues only
#check cardinal.prod_const
#check cardinal.prod_le_prod -- for universe issues only
#check cardinal.prod_eq_zero -- for universe issues only
#check cardinal.prod_ne_zero -- for universe issues only
#check cardinal.lift_prod
#check cardinal.lift_supr -- for universe issues only
#check cardinal.to_nat_finset_prod
#check cardinal.sum_lt_prod -- for universe issues only

-- ordinal.arithmetic
#check ordinal.supr_ord -- for universe issues only

-- cardinal.ordinal
#check cardinal.prod_eq_two_power

-- ordinal.cofinality
#check ordinal.supr_lt_lift -- for universe issues only
#check ordinal.supr_lt -- for universe issues only
#check cardinal.supr_lt_lift_of_is_regular
#check cardinal.supr_lt_of_is_regular
#check cardinal.sum_lt_lift_of_is_regular
#check cardinal.sum_lt_of_is_regular
#check ordinal.supr_lt_lift
#check ordinal.supr_lt
#check cardinal.supr_lt_lift_of_is_regular
#check cardinal.supr_lt_of_is_regular
#check cardinal.sum_lt_lift_of_is_regular
#check cardinal.sum_lt_of_is_regular

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
