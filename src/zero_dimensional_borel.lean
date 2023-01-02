import borel_hierarchy
import topology.separation

open topological_space

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

/- Random lemma (originally w/o the prime) now using typeclass -/
lemma tot_sep_of_zero_dim' [h : zero_dim_space α]:
  totally_separated_space α :=
begin
  constructor,
  rintros x - y - hxy,
  obtain ⟨u, v, hu, hv, xu, yv, disj⟩ := t2_separation hxy,
  obtain ⟨w, hw : is_clopen w, xw, wu⟩ := (is_topological_basis.mem_nhds_iff h.has_clopen_basis).1
    (is_open.mem_nhds hu xu),
  refine ⟨w, wᶜ, hw.1, hw.compl.1, xw, λ h, disj ⟨wu h, yv⟩, _, disjoint_compl_right⟩,
  rw set.union_compl_self,
end

end profinite

section locally_compact

variables {H : Type*} [topological_space H] [locally_compact_space H] [t2_space H]

/- Application of the random lemma, now using an instance -/

instance zero_dim_space_of_totally_disconnected [totally_disconnected_space H] : zero_dim_space H := ⟨loc_compact_Haus_tot_disc_of_zero_dim⟩

theorem loc_compact_t2_tot_disc_iff_tot_sep' :
  totally_disconnected_space H ↔ totally_separated_space H :=
begin
  split,
  { introI h,
    exact tot_sep_of_zero_dim', },
  apply totally_separated_space.totally_disconnected_space,
end

end locally_compact