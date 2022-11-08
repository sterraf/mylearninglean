import set_theory.cardinal.ordinal

open_locale cardinal -- to have notation `ℵ₀`. Plain `open` won't work
open cardinal -- for the namespace

#check (ℵ₀ : cardinal.{0})

#check (ℵ₀ : cardinal.{1}) = (ℵ₀ : cardinal)
-- #check (ℵ₀ : cardinal.{2}) = (ℵ₀ : cardinal.{1}) -- fails
#check (ℵ₀ : cardinal.{2}) = lift.{2 1} (ℵ₀ : cardinal.{1})

example : (ℵ₀ : cardinal.{2}) = lift.{2 1} (ℵ₀ : cardinal.{1}) := by { simp }

namespace cardinal

universes u v 

instance coe_card_1 : has_coe cardinal.{u} cardinal.{u+1} := ⟨cardinal.lift.{u+1 u}⟩

end cardinal

#check (ℵ₀ : cardinal.{19}) =  (ℵ₀ : cardinal.{3})

example : (ℵ₀ : cardinal.{19}) =  (ℵ₀ : cardinal.{3}) :=
begin
  unfold coe lift_t has_lift_t.lift coe_t has_coe_t.coe coe_b has_coe.coe,
  simp,
end

