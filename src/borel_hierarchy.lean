import measure_theory.measurable_space
import set_theory.cardinal.ordinal

open measurable_space
open ordinal cardinal set

universe u 
variables {α : Type u} (s : set (set α))

namespace basic_pointclasses

section rec_gen

@[reducible]
noncomputable def ordω₁ := (aleph 1 : cardinal.{u}).ord

local notation `ω₁` := ordω₁.out.α
local notation `<ω₁` := ordω₁.out.r
local notation `woω₁` := ordω₁.out.wo

lemma zero_lt_aleph_1_ord : 0 < ordω₁ := ordinal.pos_iff_ne_zero.mpr (aleph 1).ord.ne_zero_of_out_nonempty

lemma type_out_r (a : ordinal): type a.out.r = a :=
type_lt a

noncomputable def minω₁ : ω₁ :=  @enum ω₁ <ω₁ woω₁ 0 
  (by { simp only [type_out_r, zero_lt_aleph_1_ord] })

lemma not_lt_min_omega1 (i : ω₁) : ¬(i < minω₁) :=
 not_lt_of_le (enum_zero_le' zero_lt_aleph_1_ord i)

@[protected]
def sigma0_pi0_rec : ω₁ → set (set α) × set (set α)
| i :=
  let 
    P_old := ⋃ j : Iio i, (sigma0_pi0_rec j.1).snd,
    S := s ∪ {∅} ∪  set.range (λ (f : ℕ → P_old), ⋃ n, (f n).1),
    P := compl '' S
  in
    ⟨S , P⟩
using_well_founded {dec_tac := `[exact j.2]}

def sigma0 (i : ω₁) : set (set α) := (sigma0_pi0_rec s i).fst

def pi0 (i : ω₁) : set (set α) := (sigma0_pi0_rec s i).snd

theorem sigma0_pi0_rec_def' (i : ω₁) : sigma0_pi0_rec s i = ⟨sigma0 s i, pi0 s i⟩ := by { unfold pi0 sigma0, simp }

theorem pi0_sub_sigma0 (i k : ω₁) (hik : i < k) : pi0 s i ⊆ sigma0 s k :=
begin
  have : i ∈ Iio k := by simp [hik],
  unfold sigma0 sigma0_pi0_rec,
  apply subset_union_of_subset_right,
  intros x hx,
  apply mem_range.mpr,
  have hx : x ∈ ⋃ j : Iio k, (sigma0_pi0_rec s j.1).snd,
  { simp,
    use i,
    exact ⟨hik,hx⟩ },
  existsi (λn : ℕ, (⟨x,hx⟩ : ⋃ j : Iio k, (sigma0_pi0_rec s j.1).snd)),
  exact Union_const x,
end

theorem self_subset_sigma0 (i : ω₁) :
  s ⊆ sigma0 s i :=
begin
  unfold sigma0 sigma0_pi0_rec,
  apply_rules [subset_union_of_subset_left],
  exact subset_rfl
end

theorem compl_self_subset_pi0 (i : ω₁) :
  compl '' s ⊆ pi0 s i :=
begin
  unfold pi0 sigma0_pi0_rec, simp only,
  rw [image_union,image_union],
  apply_rules [subset_union_of_subset_left],
  exact subset_rfl
end

theorem empty_mem_sigma0 (i : ω₁) :
  ∅ ∈ sigma0 s i :=
begin
  unfold sigma0 sigma0_pi0_rec, simp only,
  exact mem_union_left _ (mem_union_right _ (mem_singleton ∅))
end

theorem univ_mem_pi0 (i : ω₁) :
set.univ ∈ pi0 s i := by { unfold pi0 sigma0_pi0_rec, simp }

end rec_gen

end basic_pointclasses

namespace pointclasses

/--
Same as `basic_pointclasses.sigma0_pi0_rec`, but using plain ordinals.
-/
@[protected]
def sigma0_pi0_rec : ordinal.{u} → set (set α) × set (set α)
| i :=
  let 
    P_old := ⋃ j (hij : j < i), (sigma0_pi0_rec j).snd,
    S := s ∪ {∅} ∪  set.range (λ (f : ℕ → P_old), ⋃ n, (f n).1),
    P := compl '' S
  in
    ⟨S , P⟩
using_well_founded {dec_tac := `[exact hij]}

def sigma0 (i : ordinal.{u}) : set (set α) := (sigma0_pi0_rec s i).fst

def pi0 (i : ordinal.{u}) : set (set α) := (sigma0_pi0_rec s i).snd

theorem sigma0_pi0_rec_def' (i : ordinal.{u}) : sigma0_pi0_rec s i = ⟨sigma0 s i, pi0 s i⟩ := by { unfold pi0 sigma0, simp }

theorem pi0_sub_sigma0 (i k : ordinal.{u}) (hik : i < k) : pi0 s i ⊆ sigma0 s k :=
begin
  unfold sigma0 sigma0_pi0_rec,
  apply subset_union_of_subset_right,
  intros x hx,
  apply mem_range.mpr,
  have hx : x ∈ ⋃ j < k, (sigma0_pi0_rec s j).snd,
  { simp,
    use i,
    exact ⟨hik,hx⟩ },
  existsi (λn : ℕ, (⟨x,hx⟩ : ⋃ j < k, (sigma0_pi0_rec s j).snd)),
  exact Union_const x,
end

theorem self_subset_sigma0 (i : ordinal.{u}) :
  s ⊆ sigma0 s i :=
begin
  unfold sigma0 sigma0_pi0_rec,
  apply_rules [subset_union_of_subset_left],
  exact subset_rfl
end

theorem compl_self_subset_pi0 (i : ordinal.{u}) :
  compl '' s ⊆ pi0 s i :=
begin
  unfold pi0 sigma0_pi0_rec, simp only,
  rw [image_union,image_union],
  apply_rules [subset_union_of_subset_left],
  exact subset_rfl
end

theorem empty_mem_sigma0 (i : ordinal.{u}) :
  ∅ ∈ sigma0 s i :=
begin
  unfold sigma0 sigma0_pi0_rec, simp only,
  exact mem_union_left _ (mem_union_right _ (mem_singleton ∅))
end

theorem univ_mem_pi0 (i : ordinal.{u}) :
set.univ ∈ pi0 s i := by { unfold pi0 sigma0_pi0_rec, simp }

end pointclasses

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
