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

namespace inductive_generate

open set

universe u
variables {α : Type u} (s : set (set α))

-- Experimenting with the code provided by Junyan Xu
inductive generate_from (s : set (set α)) : ordinal.{u} → set α → Prop
| basic : ∀ o (u ∈ s), generate_from o u
| empty : ∀ o, generate_from o ∅
| compl : ∀ o u (o' < o), generate_from o' u → generate_from o uᶜ
| union : ∀ o (f : ℕ → set α) (o' : ℕ → ordinal.{u}), (∀ n, o' n < o) →
  (∀ n, generate_from (o' n) (f n)) → generate_from o (⋃ i, f i)

def gen_from_set' (s : set (set α)) : ordinal.{u} → set (set α) := generate_from s

example : gen_from_set' s 0 = s ∪ {∅}:=
begin
  unfold gen_from_set',
  ext, split;
  intro hx,
  { cases hx with _ _ hxins o' o x o ho gensx _ f o' ho'lt geno'f,
    -- record the variables above.
    { exact mem_union_left _ hxins },
    { finish },
    { exfalso,
      exact ordinal.not_lt_zero _ ho },
    { exfalso,
      exact ordinal.not_lt_zero _ (ho'lt 0) },
  },
  { cases hx,
    { exact generate_from.basic 0 x hx }, -- Is there be a better inductive way
    { simp at hx,
      rw hx,
      exact generate_from.empty 0 } } -- than using these `exact`s?
end

/--
First attempt to prove an induction lemma for `generate_from`.
-/
lemma generate_from_induction (s : set (set α)) (P : set α → Prop) (i : ordinal.{u}) (x : set α)
(h_basic : ∀ (x ∈ s), P x)
(h_empty : P ∅)
(h_compl : ∀x, P x → P (xᶜ))
(h_union : ∀ (f : ℕ → set α), (∀ n, P (f n)) → P (⋃ i, f i)) (hsox: generate_from s i x) : P x :=
begin
  induction hsox with o y hxins o' o y o' ho'o gensx IH o f h hnlto genhf IH,
  exacts [h_basic y hxins, h_empty, h_compl y IH, h_union f IH]
end

end inductive_generate

namespace cardinal

universes u v 

def equiv_ulift {α β : Type*} (heq : α ≃ β) : (ulift.{u} α) ≃ (ulift.{v} β) :=
begin
  cases heq with tofu infu li ri,
  let ntf := λ (x : ulift.{u} α), ulift.up.{v} (tofu x.down),
  let nif := λ (x : ulift.{v} β), ulift.up.{u} (infu x.down),
  have ntfx : ∀x, ntf x = ulift.up.{v} (tofu x.down) := by simp,
  have nify : ∀y, nif y = ulift.up.{u} (infu y.down) := by simp,
  have nli : function.left_inverse nif ntf,
  { intro x,
    rw [ntfx, nify, li x.down, ulift.up_down] },
  have nri : function.right_inverse nif ntf,
  { intro x,
    rw [ntfx, nify, ri x.down, ulift.up_down] },
  exact ⟨ntf, nif, nli, nri⟩
end

end cardinal