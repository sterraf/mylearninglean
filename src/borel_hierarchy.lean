import set_theory.cardinal.ordinal

universe u 

namespace ordinal

open cardinal 
/--
The first uncountable ordinal in type universe `u`.
-/
@[reducible]
noncomputable def ω₁ := (aleph 1 : cardinal.{u}).ord

end ordinal

namespace pointclasses

section sigma0_pi0

open set

parameters {α : Type u} (s : set (set α))
variables (i k : ordinal.{u})

/--
Simultaneous recursive definition of Σ⁰ᵢ and Π⁰ᵢ pointclasses by recursion
on ordinals (a variant of 11.B in Kechris, _Classical Descriptive Set Theory_).

The main difference is that the hierarchy starts at level 0: Π⁰₀ are intended to be basic open sets and Σ⁰₀ is the empty family.
-/
@[protected]
def sigma0_pi0_rec : ordinal.{u} → set (set α) × set (set α)
| i :=
    let 
      P_old := ⋃ j (hij : j < i), (sigma0_pi0_rec j).snd,
      S := if i = 0 then ∅ else set.range (λ (f : ℕ → P_old), ⋃ n, (f n).1),
      P := if i = 0 then s else compl '' S
    in
      ⟨S , P⟩
using_well_founded {dec_tac := `[exact hij]}

def sigma0 (i : ordinal.{u}) : set (set α) := (sigma0_pi0_rec i).fst

def pi0 : set (set α) := (sigma0_pi0_rec i).snd

lemma sigma0_pi0_rec_def' :
  sigma0_pi0_rec i = ⟨sigma0 i, pi0 i⟩ :=
by { unfold pi0 sigma0, simp } -- without the enveloping namespace, `unfold` fails

lemma sigma0_eq_Union_pi0:
  sigma0 i = set.range (λ (f : ℕ → ⋃ j (hij : j < i), pi0 j), ⋃ n, (f n).1) :=
begin
  rcases classical.em (i=0) with hi | hi;
  unfold sigma0 sigma0_pi0_rec,
  { rw hi, apply eq.symm, simp [range_eq_empty, ordinal.not_lt_zero] },
  { simp [hi], congr }
end

lemma pi0_subset_sigma0 (hik : i < k) :
  pi0 i ⊆ sigma0 k :=
begin
  simp only [sigma0_eq_Union_pi0,hik],
  intros x hx,
  apply mem_range.mpr,
  have hxU : x ∈ ⋃ j < k, pi0 s j,
  { simp,
    use i,
    exact ⟨hik,hx⟩ },
  existsi (λn : ℕ, (⟨x,hxU⟩ : ⋃ (j : ordinal) (hij : j < k), pi0 s j)),
  exact Union_const x
end

lemma pi0_eq_compl_sigma0 (hi : i ≠ 0):
  pi0 i = compl '' sigma0 i :=
by { unfold sigma0 pi0 sigma0_pi0_rec, simp [hi] }

lemma sigma0_zero :
  sigma0 0 = ∅ :=
by { unfold sigma0 sigma0_pi0_rec, simp }

lemma pi0_zero :
  pi0 0 = s :=
by { unfold pi0 sigma0_pi0_rec, simp }

lemma sigma0_one :
  sigma0 1 = set.range (λ (f : ℕ → s), ⋃ n, (f n).1) :=
begin
  unfold sigma0 sigma0_pi0_rec, simp,
  ext z, simp,
  refine ⟨λ h, _, λ h, _⟩;
  rcases h with ⟨f,hf⟩,
  { have f_in_s : ∀ n : ℕ, ↑(f n) ∈ s,
    intro n,
    rcases (mem_Union.mp (f n).property) with ⟨j,hf⟩,
    rw ordinal.lt_one_iff_zero at hf,
    simp at hf,
    have j_0 := hf.left,
    rw [j_0,sigma0_pi0_rec_def',pi0_zero] at hf,
    exact hf.right,
    use (λn, ⟨f n, f_in_s n⟩ : ℕ → ↥s),
    exact hf },
  { have Un_eq_s : (⋃ (j : ordinal) (hj : j < 1), (sigma0_pi0_rec s j).snd) = s,
    { simp [ordinal.lt_one_iff_zero, sigma0_pi0_rec_def', pi0_zero] },
    have f_in_s : ∀ (n : ℕ), ↑(f n) ∈ s := λn, (f n).property,
    have f_in_Un : ∀ (n : ℕ), ↑(f n) ∈ (⋃ (j : ordinal) (hj : j < 1), (sigma0_pi0_rec s j).snd),
    simp [Un_eq_s],
    use (λn, ⟨f n, f_in_Un n⟩ : ℕ → ↥(⋃ (j : ordinal) (hj : j < 1), (sigma0_pi0_rec s j).snd)),
    simp [hf] }
end

lemma sigma0_subset_sigma0 (hik : i ≤ k) :
  sigma0 i ⊆ sigma0 k :=
begin
  rw le_iff_lt_or_eq at hik,
  cases hik,
  -- Take care of the trivial case `i = k` first,
  swap,
  { simp [hik, subset_rfl] },
  -- Now the interesting `i < k`:
  repeat { rw sigma0_eq_Union_pi0 },
  intros x hx,
  cases hx with f hf,
  simp only at hf,
  have hfUn : ∀ (n : ℕ), ↑(f n) ∈ (⋃ j < k, pi0 s j),
  { intro n,
    apply mem_Union.mpr,
    -- Awful proof ahead :(
    have : ∃ j (hjk : j < k), (f n).val ∈ pi0 s j :=
      (let (Exists.intro j q) := (mem_Union.mp (f n).property) in
        let (Exists.intro l r) := mem_Union.mp q in
        Exists.intro j (Exists.intro (trans l hik) r)),
    cases this with j hj,
    use j,
    exact mem_Union.mpr hj },
  apply mem_range.mpr,
  existsi (λn : ℕ, (⟨f n, hfUn n⟩ : ⋃ j < k, (pi0 s j))),
  tauto,
end

/--
The hypothesis `i ≠ 0` is required in case elements of the generating set are
not closed. If the underlying space is zero-dimensional, one can take a basis
of clopen sets and the inclusion will hold unconditionally. 
-/
lemma pi0_subset_pi0 (hi : i ≠ 0) (hik : i ≤ k) :
  pi0 i ⊆ pi0 k :=
begin
  rw [pi0_eq_compl_sigma0,pi0_eq_compl_sigma0],
  exacts [image_subset _ (sigma0_subset_sigma0 s i k hik),
    ordinal.one_le_iff_ne_zero.mp (trans (ordinal.one_le_iff_ne_zero.mpr hi) hik),
    hi] 
end

end sigma0_pi0
end pointclasses

section inductive_generate

open set

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