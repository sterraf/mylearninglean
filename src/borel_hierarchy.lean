import measure_theory.measurable_space
import set_theory.cardinal.ordinal

open measurable_space
open ordinal cardinal set

namespace basic_pointclasses

section rec_gen

universe u 
parameter (X : Type*)
variable (g : set (set X))
variable {α : Type u}

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

def sigma0_pi0_rec (s : set (set α)) : ω₁ → set (set α) × set (set α)
| i :=
  let 
    P_old := ⋃ j : Iio i, (sigma0_pi0_rec j.1).snd,
    S := s ∪ {∅} ∪  set.range (λ (f : ℕ → P_old), ⋃ n, (f n).1),
    P := compl '' S
  in
    ⟨S , P⟩
using_well_founded {dec_tac := `[exact j.2]}

def sigma0 (s : set (set α)) (i : ω₁) : set (set α) := (sigma0_pi0_rec s i).fst

def pi0 (s : set (set α)) (i : ω₁) : set (set α) := (sigma0_pi0_rec s i).snd

theorem sigma0_pi0_rec_def' (s : set (set α)) (i : ω₁) : sigma0_pi0_rec s i = ⟨sigma0 s i, pi0 s i⟩ := by { unfold pi0 sigma0, simp }

theorem pi0_sub_sigma0 (s : set (set α)) (i k : ω₁) (hik : i < k) : pi0 s i ⊆ sigma0 s k := 
begin
  have : i ∈ Iio k := by simp [hik],
  unfold sigma0 sigma0_pi0_rec,
  apply subset_union_of_subset_right,
  intros x hx,
  apply mem_range.mpr,
  have : x ∈ ⋃ j : Iio k, (sigma0_pi0_rec s j.1).snd,
  { simp,
    use i,
    exact ⟨hik,hx⟩ },
  existsi (λn : ℕ, ↑x),
  { simp, ext z, simp,
    split,
    { intro hz1,
      cases hz1 with i hz,
      sorry },
    { intro hx,
      use 0,
      sorry } },
  sorry
end

theorem self_subset_sigma0 (s : set (set α)) (i : ω₁) :
  s ⊆ sigma0 s i :=
begin
  unfold sigma0 sigma0_pi0_rec,
  apply_rules [subset_union_of_subset_left],
  exact subset_rfl
end

theorem compl_self_subset_pi0 (s : set (set α)) (i : ω₁) :
  compl '' s ⊆ pi0 s i :=
begin
  unfold pi0 sigma0_pi0_rec, simp only,
  rw [image_union,image_union],
  apply_rules [subset_union_of_subset_left],
  exact subset_rfl
end

theorem empty_mem_sigma0 (s : set (set α)) (i : ω₁) :
  ∅ ∈ sigma0 s i :=
begin
  unfold sigma0 sigma0_pi0_rec, simp only,
  exact mem_union_left _ (mem_union_right _ (mem_singleton ∅))
end

theorem univ_mem_pi0 (s : set (set α)) (i : ω₁) : 
set.univ ∈ pi0 s i := by { unfold pi0 sigma0_pi0_rec, simp }

end rec_gen

end basic_pointclasses
