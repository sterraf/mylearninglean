import borel_hierarchy
import topology.separation
import topology.bases

open topological_space

namespace borel_class

open set pointclass

variables {α : Type*} [topological_space α] [second_countable_topology α]

/-
def sigma0_pi0_rec : ordinal → bool → set α → Prop :=
  pointclass.sigma0_pi0_rec (countable_basis α)

def sigma0 : ordinal → set (set α) := pointclass.sigma0 (countable_basis α)

def pi0 : ordinal → set (set α) := pointclass.pi0 (countable_basis α)
-/

lemma sigma0_one : sigma0 (countable_basis α) 1 = {u : set α | is_open u} :=
begin
  ext z, refine ⟨λ hz, _, λ hz, _⟩,
  { rw pointclass.sigma0_one at hz,
    simp only [mem_range, mem_set_of_eq] at *,
    rcases hz with ⟨y, rfl⟩,
    apply is_open_Union,
    intro i,
    rcases (y i).property with h | h | h,
    { exact is_open_of_mem_countable_basis h },
    { rw h, exact is_open_empty },
    { simp only [mem_singleton_iff, subtype.val_eq_coe] at *,
      rw h, exact is_open_univ } },
  { rw [mem_set_of_eq,
      is_topological_basis.open_iff_eq_sUnion (is_basis_countable_basis α)] at hz,
    rcases hz with ⟨S, hS, hz⟩,
    rw pointclass.sigma0_one,
    rcases classical.em (S=∅) with rfl | nonemp,
    { existsi λ n, (⟨∅, _⟩ : ↥(countable_basis α ∪ {∅, univ})),
      { simp only [Union_empty],
        rw sUnion_empty at hz,
        exact hz.symm },
      { simp only [mem_insert_iff, true_or, eq_self_iff_true, union_insert, union_singleton] } },
    { rw sUnion_eq_Union at hz,
      have Sc : S.countable := countable.mono hS (countable_basis α).to_countable,
      have gsurj : ∃ (g : ℕ → S), g.surjective :=
        (set.countable_iff_exists_surjective (nonempty_iff_ne_empty.mpr nonemp)).mp Sc,
      cases gsurj with g hg,
      use inclusion (subset_union_of_subset_left hS {∅, univ}) ∘ g,
      simp only [subtype.val_eq_coe, coe_inclusion],
      rw ← Union_congr_of_surjective g hg at hz,
      swap 3,
      exacts [λ n, (g n).val, hz.symm, λ n, eq.refl (g n)] } }
end

lemma pi0_one : pi0 (countable_basis α) 1 = {u : set α | is_closed u} :=
begin
  rw [pi0_eq_compl_sigma0 _ _ (zero_ne_one).symm, sigma0_one],
  ext z, refine ⟨λ hz, _, λ hz, _⟩,
  { rcases hz with ⟨x, hx, co⟩,
    rw eq_compl_comm.mp (eq.symm co) at hx,
    exact ⟨hx⟩ },
  { change is_closed z at hz,
    change ∃ (x : set α), is_open x ∧ xᶜ = z,
    use zᶜ,
    simp only [compl_compl, is_open_compl_iff, and_true, eq_self_iff_true, hz] }
end

/-- The *ambiguous* Borel classes, comprising sets that are both `sigma0` and `pi0`. -/
def delta0 (i : ordinal) : set (set α) := sigma0 (countable_basis α) i ∩ pi0 (countable_basis α) i

lemma delta0_one : delta0 1 = {u : set α | is_clopen u} :=
by { rw [delta0, sigma0_one, pi0_one], tauto }

end borel_class

section zero_dim_space

variables (α : Type*) [topological_space α]

/-- The clopen subsets form a basis of the topology. -/
def has_clopen_basis : Prop := is_topological_basis {s : set α | is_clopen s}

/-- A space is zero-dimensional if it is T₂ and has a basis consisting of clopens. -/
class zero_dim_space (α : Type*) [topological_space α] [t2_space α] : Prop :=
(has_clopen_basis : has_clopen_basis α)

end zero_dim_space

variables {α : Type*} [topological_space α]

section profinite

variables [t2_space α]

/- Old mathlib lemma recovered using typeclass -/
lemma tot_sep_of_zero_dim [h : zero_dim_space α] :
  totally_separated_space α :=
  totally_separated_space_of_t1_of_basis_clopen h.has_clopen_basis

end profinite

section locally_compact

variables {H : Type*} [topological_space H] [locally_compact_space H] [t2_space H]

/- Application of the random lemma, now using an instance -/

instance zero_dim_space_of_totally_disconnected [totally_disconnected_space H] : 
  zero_dim_space H := ⟨loc_compact_Haus_tot_disc_of_zero_dim⟩

theorem loc_compact_t2_tot_disc_iff_tot_sep' :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { introI h,
    exact tot_sep_of_zero_dim, },
  apply totally_separated_space.totally_disconnected_space,
end

end locally_compact