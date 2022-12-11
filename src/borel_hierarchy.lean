import set_theory.cardinal.cofinality
import measure_theory.measurable_space_def
import set_theory.cardinal.continuum

universe u 

namespace ordinal

open cardinal 

/--
The first uncountable ordinal in type universe `u`.
-/
@[reducible]
noncomputable def ω₁ := (aleph 1 : cardinal.{u}).ord

lemma omega_lt_omega1 :
  omega < ω₁ :=
begin
  have := (ord_lt_ord.mpr (aleph_0_lt_aleph_one)),
  rw ord_aleph_0 at this,
  exact this
end

end ordinal

open set

namespace cardinal
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
  have Y : (⋃ j < i, A j) = (⋃ (j : Iio i), A j),
  { simp },
  have Z : #(↥⋃ j < i, A j) = #(↥⋃ (j : Iio i), A j),
  { rw Y },
  rw Z,
  clear Y Z,
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
lemma mk_Union_lt_of_lt_cof {β : Type u} (κ : cardinal.{u}) (i : ordinal.{u}) (hi : i < κ.ord.cof.ord) (A : ordinal → set β) (hκ : ∀ j < i, #↥(A j) < κ) :
  #(↥⋃ j < i, A j) < κ :=
-/

end cardinal

namespace pointclasses

section sigma0_pi0

open set

parameters {α : Type u} (s : set (set α))
variables (i k : ordinal.{u})

/--
Simultaneous recursive definition of Σ⁰ᵢ and Π⁰ᵢ pointclasses by recursion
on ordinals (a variant of 11.B in Kechris, _Classical Descriptive Set Theory_).

The main difference is that the hierarchy starts at level 0: Π⁰₀ are intended to
be basic open sets (augmented with `∅` and `univ`) and Σ⁰₀ is the empty family.
-/

inductive sigma0_pi0_rec {α : Type u} (s : set (set α)) :
  ordinal.{u} → bool → set α → Prop
| basic (x ∈ s) : sigma0_pi0_rec 0 tt x
| empty         : sigma0_pi0_rec 0 tt ∅
| univ          : sigma0_pi0_rec 0 tt set.univ
| compl {i x}   : sigma0_pi0_rec i ff x → sigma0_pi0_rec i tt xᶜ
| union {i} (f : ℕ → set α) (g : ℕ → ordinal.{u}) :
    (∀ n, g n < i) → (∀ n, sigma0_pi0_rec (g n) tt (f n)) → sigma0_pi0_rec i ff (⋃ n, f n)

def sigma0 : set (set α) := sigma0_pi0_rec i ff

def pi0 : set (set α) := sigma0_pi0_rec i tt

lemma sigma0_pi0_rec_def' {b : bool} :
  sigma0_pi0_rec i b = if b then pi0 i else sigma0 i :=
by { unfold pi0 sigma0, cases b; refl }

@[simp]
lemma sigma0_zero :
  sigma0 0 = ∅ :=
begin
  unfold sigma0,
  ext x, simp,
  intro hx,
  cases hx with _ _ _ _ _ _ f g glt hf,
  exact ordinal.not_lt_zero (g 0) (glt 0)
 end
 
lemma sigma0_eq_Union_pi0:
  sigma0 i = set.range (λ (f : ℕ → ⋃ j (hij : j < i), pi0 j), ⋃ n, (f n).1) :=
begin
  rcases classical.em (i=0) with rfl | hi;
  unfold sigma0,
  rw sigma0_pi0_rec_def',
  { apply eq.symm, simp [range_eq_empty, ordinal.not_lt_zero] },
  { simp [hi],
    ext x, split; intro hx,
    { cases hx with _ _ _ _ _ _ f g glt hf,
      existsi λn, (⟨f n, _⟩ : ↥⋃ j < i, pi0 s j),
      swap, 
      { simp,
        use g n,
        exact ⟨glt n, hf n⟩ },
      simp,
      ext x, split; intro hx,
      exacts [mem_Union.mp hx, mem_Union.mpr hx] },
    { cases hx with f hf,
      rw ← hf,
      simp at hf,
      choose g hg using λn, (mem_Union.mp (f n).property),
      simp at hg,
      apply sigma0_pi0_rec.union _ g,
      exact λ n, (hg n).1,
      unfold pi0 at hg,
      exact λ n, (hg n).2 } }
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
  existsi (λn : ℕ, (⟨x,hxU⟩ : ⋃ (j < k), pi0 s j)),
  exact Union_const x
end

lemma pi0_eq_compl_sigma0 (hi : ¬i = 0):
  pi0 i = compl '' sigma0 i :=
begin
  unfold sigma0 pi0,
  ext x, split; intro hx; cases hx with hcomp IH c d IH,
  { contradiction },
  { contradiction },
  { contradiction },
  { simp, use d, tauto },
  { have := sigma0_pi0_rec.compl IH.1,
    rw ← IH.2,
    assumption }
end  

lemma pi0_zero :
  pi0 0 = s ∪ {∅,univ} :=
begin
  unfold pi0, ext, simp, split; intro hx,
  { cases hx with _ hx _ v hv,
    any_goals { tauto },
    simp [sigma0_pi0_rec_def'] at hv,
    have : sigma0 s 0 v,
    { exact hv },
    exfalso,
    rw sigma0_zero at this,
    exact this },
  { rcases hx with rfl | rfl | x_in_s,
    exacts [sigma0_pi0_rec.empty, sigma0_pi0_rec.univ, sigma0_pi0_rec.basic x x_in_s] }
end

lemma sigma0_one :
  sigma0 1 = set.range (λ (f : ℕ → s ∪ {∅,univ}), ⋃ n, (f n).1) :=
begin
  unfold sigma0, simp,
  ext z, simp,
  refine ⟨λ h, _, λ h, _⟩,
  swap,
  { rcases h with ⟨f,rfl⟩,
    apply sigma0_pi0_rec.union (λ n, (f n).val) (λ n, 0),
    { simp },
    { simp,
      intro n,
      have hfn := (f n).property,
      simp at hfn,
      rcases hfn with nul | uni | bas,
      { rw nul, exact sigma0_pi0_rec.empty },
      { rw uni, exact sigma0_pi0_rec.univ },
      { exact sigma0_pi0_rec.basic (f n) bas } } },
  { set o := (1 : ordinal) with ho,
    replace h : sigma0_pi0_rec o ff z,
    { tauto },
    clear_value o,
    cases h with _ _ _ _ _ _ f g glt hf,
    subst ho,
    have gnul : ∀ n, g n = 0,
    { exact λ n, ordinal.lt_one_iff_zero.mp (glt n) },
    simp_rw gnul at hf,
    have sigtt0 : ∀ n, f n ∈ (s ∪ {∅, univ}),
    { have := pi0_zero s,
      unfold pi0 at this,
      rw this at hf, 
      exact hf },
    use λ n, ⟨f n, sigtt0 n⟩,
    simp,
    ext x, split; intro hx,
    exacts [mem_Union.mp hx, mem_Union.mpr hx] }
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
The sequence of `pi0` families is nondecreasing.

The hypothesis `¬i = 0` is required in case elements of the generating set are
not closed. If the underlying space is zero-dimensional, one can take a basis
of clopen sets and the inclusion will hold unconditionally. 
-/
lemma pi0_subset_pi0 (hi : ¬i = 0) (hik : i ≤ k) :
  pi0 i ⊆ pi0 k :=
begin
  rw [pi0_eq_compl_sigma0,pi0_eq_compl_sigma0],
  exacts [image_subset _ (sigma0_subset_sigma0 s i k hik),
    ordinal.one_le_iff_ne_zero.mp (trans (ordinal.one_le_iff_ne_zero.mpr hi) hik),
    hi]
end

lemma Union_of_sigma0_sequence {g : ℕ → sigma0 i} :
  (⋃ n, (g n).val) ∈ sigma0 i :=
begin
  have hg : ∀ n : ℕ, (g n).val ∈ sigma0 s i := λ n, (g n).property,
  simp [sigma0_eq_Union_pi0] at *,
  choose o ho using hg,
  have : ℕ × ℕ ≃ ℕ,
  { exact denumerable.eqv (ℕ × ℕ) },
  cases this with tup untup htup huntup,
  use λ n, let p := (untup n) in o p.1 p.2,
  ext x, split; intro hx; simp at *;
  cases hx with j hxin,
  { let n := (untup j).fst,
    use n,
    specialize ho n,
    rw ← ho,
    simp,
    use (untup j).snd,
    assumption },
  { simp [← ho j] at hxin,
    cases hxin with k hk,
    existsi tup ⟨j,k⟩,
    have fstj : (untup (tup ⟨j,k⟩)).fst = j,
    { exact (congr_arg prod.fst (htup (j, k))).trans rfl },
    have sndk : (untup (tup ⟨j,k⟩)).snd = k,
    { exact (congr_arg prod.snd (htup (j, k))).trans rfl },
    rw [fstj,sndk],
    exact hk }
end

lemma Union_of_mem_sigma0 {f : ℕ → set α} (hf : ∀ n, f n ∈ sigma0 i):
  (⋃ n, f n) ∈ sigma0 i :=
by exact @Union_of_sigma0_sequence _ s i (λn, {val := f n, property := hf n} : ℕ → sigma0 s i)

lemma self_subset_sigma0 (hi : ¬i = 0) :
  s ⊆ sigma0 i :=
begin
  calc
  s   ⊆ s ∪ {∅,univ} : subset_union_left _ _
  ... = pi0 s 0      : eq.symm (pi0_zero s)
  ... ⊆ sigma0 s i   : pi0_subset_sigma0 s 0 i (ordinal.pos_iff_ne_zero.mpr hi),
end

theorem empty_mem_sigma0 (hi : ¬i = 0) :
  ∅ ∈ sigma0 i :=
begin
  have : ∅ ∈ s ∪ {∅,univ} := by { apply mem_union_right, simp },
  have that : s ∪ {∅,univ} = pi0 s 0 := eq.symm (pi0_zero s),
  rw that at this,
  calc
  ∅   ∈ pi0 s 0      : this
  ... ⊆ sigma0 s i   : pi0_subset_sigma0 s 0 i (ordinal.pos_iff_ne_zero.mpr hi)
end

end sigma0_pi0

section gen_measurable

parameters {α : Type u} (s : set (set α))
variables (i k : ordinal.{u})

open set ordinal cardinal

lemma sup_sequence_lt_omega1 (o : ℕ → ordinal.{u}) (ho : ∀ n, o n < ω₁):
  sup o < ω₁ :=
begin
  apply sup_lt_ord_lift _ ho,
  simp,
  rw [cardinal.is_regular_aleph_one.cof_eq],
  exact aleph_0_lt_aleph_one,
end

lemma is_limit_omega1 :
  ω₁.is_limit := ord_is_limit (aleph_0_le_aleph 1)

/--
Denumerably many elements chosen from a nondecreasing `ω₁`-sequence of sets,
all lie in one of the sets.
-/
lemma bound_omega1_of_increasing_of_sequence {β : Type*} {A : ordinal → set β}
  {hA : ∀ j k (hjk : j ≤ k), A j ⊆ A k}
  {f : ℕ → β} (hf : ∀ n, ∃ i, i < ω₁ ∧ f n ∈ A i) :
  ∃ i (hi : i < ω₁), ∀ n, f n ∈ A i :=
begin
  choose o ho using hf,
  use sup o,
  split,
  { finish [sup_sequence_lt_omega1] },
  intro n,
  specialize ho n,
  specialize hA (o n) (sup o) (le_sup o n),
  tauto
end

/--
The σ-algebra generated by the family `s`. It is obtained at the `ω₁`th level
of the `sigma0` hierarchy.
-/
def gen_measurable := sigma0 s ω₁

lemma gen_measurable_eq_Union_sigma0 :
  gen_measurable = ⋃ (j < ω₁), sigma0 s j :=
begin
  unfold gen_measurable,
  apply subset_antisymm,
  { rw sigma0_eq_Union_pi0,
    intros x hx,
    simp at *,
    cases hx with f hf,
    let g := λ n, (f n).property,
    simp at g,
    choose o ho using g,
    use order.succ(sup o),
    split,
    { exact is_limit.succ_lt is_limit_omega1 (sup_sequence_lt_omega1 o (λ n, (ho n).left)) },
    rw sigma0_eq_Union_pi0,
    simp,
    have typf : ∀ n, ↑(f n) ∈ ⋃ (j < order.succ (sup o)), pi0 s j,
    { intro n, apply mem_Union.2,
      specialize ho n,
      use o n,
      exact mem_Union.2 ⟨lt_of_le_of_lt (le_sup o n) (order.lt_succ (sup o)), ho.2⟩ },
    use λ n, (⟨f n, typf n⟩ : ⋃ (j < order.succ (sup o)), pi0 s j),
    tauto },
  { simp,
    exact λ _ hi, sigma0_subset_sigma0 s _ _ (le_of_lt hi) }
end 

theorem compl_mem_gen_measurable (t : set α) (ht : t ∈ gen_measurable) :
  tᶜ ∈ gen_measurable :=
begin
  rw gen_measurable_eq_Union_sigma0 at ht,
  simp at ht,
  cases ht with o ho,
  rcases classical.em (o=0) with rfl | onon,
  { finish },
  calc
  tᶜ  ∈ pi0 s o          : by { rw pi0_eq_compl_sigma0, simp, exacts [ho.2,onon] }
  ... ⊆ gen_measurable s : pi0_subset_sigma0 s o ω₁ ho.1,
end

theorem Union_mem_gen_measurable {f : ℕ → set α} (hf : ∀ n, f n ∈ gen_measurable) :
  (⋃ n, f n) ∈ gen_measurable :=
by { unfold gen_measurable at *, exact Union_of_mem_sigma0 s ω₁ hf }

open measurable_space

lemma generate_measurable_of_mem_sigma0 (t) (ht : t ∈ sigma0 s i) :
  generate_measurable s t :=
begin
  induction i using ordinal.induction with i IH generalizing t,
  rw sigma0_eq_Union_pi0 at ht,
  simp at ht,
  rcases ht with ⟨f,hf⟩,
  have typf : ∀ n : ℕ, generate_measurable s (f n),
  { intro n,
    have fn_in : (f n).val ∈ ⋃ (j : ordinal) (hij : j < i), pi0 s j := (f n).property,
    simp at fn_in,
    rcases fn_in with ⟨o,⟨o_lt_i,fn_in⟩⟩,
    -- Case `(f n).val ∈ pi0 s 0`.
    rcases classical.em (o=0) with rfl | honz,
    { rw pi0_zero at fn_in,
      rcases fn_in with  fn_in | fn_emp | fn_in,
      { exact generate_measurable.basic _ fn_in },
      { rw fn_emp, exact generate_measurable.empty },
      { simp at fn_in, rw [fn_in,←compl_empty],
        exact generate_measurable.compl _ generate_measurable.empty } },
    -- Case `(f n).val ∈ pi0 s o` with `o ≠ 0`.
    simp at IH,
    rw pi0_eq_compl_sigma0 s o honz at fn_in,
    rw ← compl_compl ↑(f n),
    apply generate_measurable.compl,
    cases fn_in with x hx,
    rw [←hx.2, compl_compl],
    exact IH o o_lt_i x hx.1 },
  rw ← hf,
  exact generate_measurable.union (λn, (f n).val) typf
end

theorem generate_measurable_eq_gen_measurable :
  {t | generate_measurable s t} = gen_measurable :=
begin
  ext t, refine ⟨λ ht, _, λ ht, _⟩,
  { induction ht with u hu u hu IH f hf IH,
    exacts
    [ self_subset_sigma0 s ω₁ (ω₁.ne_zero_of_out_nonempty) hu,
      empty_mem_sigma0 s ω₁ (ω₁.ne_zero_of_out_nonempty),
      compl_mem_gen_measurable s u IH,
      Union_mem_gen_measurable s IH ]},
  { exact generate_measurable_of_mem_sigma0 s ω₁ t ht }
end

end gen_measurable

section card_gen_measurable

parameters {α : Type u} (s : set (set α))
variables (i k : ordinal.{u})

open set measurable_space cardinal      
open_locale cardinal

-- Essentially the same results in `measure_theory.card_measurable_space`.
/- The result holds for arbitrary `i`, but it is easier to prove
this way -/
lemma cardinal_sigma0_le (hi : i ≤ ordinal.ω₁):
  #(sigma0 s i) ≤ (max (#s) 2) ^ aleph_0.{u} :=
begin
  induction i using ordinal.induction with i IH,
  have Upi0sub : (⋃ j < i, pi0 s j) ⊆ s ∪ {∅, univ} ∪ ⋃ j < i, compl '' sigma0 s j,
  { simp,
    intros j hj x hx,
    rcases classical.em (j=0) with rfl | hjnz,
    { simp [pi0_zero] at hx, exact mem_union_left _ hx },
    rw pi0_eq_compl_sigma0 s j hjnz at hx,
    apply mem_union_right _ (mem_Union.mpr _),
    use j,
    apply mem_Union.mpr,
    use hj,
    exact hx },
  have cardcompl : ∀ j, #(sigma0 s j) = #(compl '' sigma0 s j) :=
    λ j, cardinal.eq.mpr (⟨equiv.set.image _ _  compl_injective⟩),
  have A := aleph_0_le_aleph 1,
  have B : aleph 1 ≤ (max (#s) 2) ^ aleph_0.{u} :=
    aleph_one_le_continuum.trans (power_le_power_right (le_max_right _ _)),
  have C : ℵ₀ ≤ (max (#s) 2) ^ aleph_0.{u} := A.trans B,
  have L : #(↥(s ∪ {∅, univ})) ≤ (max (#s) 2) ^ aleph_0.{u},
  { apply_rules [(mk_union_le _ _).trans, add_le_of_le C, mk_image_le.trans],
    { exact (le_max_left _ _).trans (self_le_power _ one_lt_aleph_0.le) },
    repeat { simp [mk_singleton], exact one_lt_aleph_0.le.trans C } },
  have K : #(↥⋃ j < i, compl '' sigma0 s j) ≤ (max (#s) 2) ^ aleph_0.{u},
  { apply mk_Union_le_of_le,
    exact (hi.trans $ ord_le_ord.mpr B),
    exact C,
    intros j hj,
    rw ← cardcompl,
    apply IH j hj,
    exact (le_of_lt $ lt_of_lt_of_le hj hi) },
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

theorem cardinal_gen_measurable_le :
  #(gen_measurable s) ≤ (max (#s) 2) ^ aleph_0.{u} := cardinal_sigma0_le _ (le_refl _)

theorem cardinal_generate_measurable_le :
  #{t | generate_measurable s t} ≤ (max (#s) 2) ^ aleph_0.{u} :=
begin
  rw generate_measurable_eq_gen_measurable,
  exact cardinal_gen_measurable_le s,
end

theorem cardinal_measurable_set_le' :
  #{t | @measurable_set α (generate_from s) t} ≤ (max (#s) 2) ^ aleph_0.{u} :=
cardinal_generate_measurable_le

theorem cardinal_generate_measurable_le_continuum (hs : #s ≤ 𝔠) :
  #{t | generate_measurable s t} ≤ 𝔠 :=
(cardinal_generate_measurable_le).trans begin
  rw ←continuum_power_aleph_0,
  exact_mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le)
end

theorem cardinal_measurable_set_le_continuum :
  #s ≤ 𝔠 → #{t | @measurable_set α (generate_from s) t} ≤ 𝔠 :=
cardinal_generate_measurable_le_continuum

end card_gen_measurable

end pointclasses
