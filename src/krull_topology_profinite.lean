import field_theory.galois 
import group_filter_basis
import topology.category.CompHaus.default

open group_filter_basis




lemma diff_equivs_have_diff_values {K L : Type*} [field K] [field L] [algebra K L]
{f g : L ≃ₐ[K] L} (h : f ≠ g) :
∃ (x : L), f x ≠ g x :=
begin
  by_contra h',
  have h'' : ∀ (x : L), ¬ (f x ≠ g x) := forall_not_of_not_exists h',
  simp at h'',
  have h_eq : f = g,
  {
    ext,
    exact h'' a,
  },
  exact h h_eq,
end


def krull_t2 (K L : Type*) [field K] [field L] [algebra K L] (h_int : 
∀ (x : L), is_integral K x):
t2_space (L ≃ₐ[K] L)  :=
{ t2 := 
begin 
  intros f g hfg,
  let φ := f⁻¹ * g,
  have h : ∃ (x : L), f x ≠ g x,
  {
    exact diff_equivs_have_diff_values hfg,
  },
  cases h with x hx,
  have hφx : φ x ≠ x,
  {
    change f⁻¹(g x) ≠ x,
    apply ne_of_apply_ne f,
    rw inv_comp f (g x),
    rw ne_comm,
    exact hx,
  },
  let E : intermediate_field K L := intermediate_field.adjoin K {x},
  let h_findim := intermediate_field.adjoin.finite_dimensional (h_int x),
end}

example {K L : Type*} [field K] [field L] [algebra K L] (x : L) (h : is_integral K x) :
finite_dimensional K (intermediate_field.adjoin K {x} : intermediate_field K L)  :=
begin
  
end

lemma krull_compact (K L : Type*) [field K] [field L] [algebra K L] :
compact_space (L ≃ₐ[K] L) :=
begin
  sorry, 
end


def krull_topology_hausdorff (K L : Type*) [field K] [field L] [algebra K L] :
CompHaus :=
{ to_Top := Top.of (L ≃ₐ[K] L),
  is_compact := krull_compact K L,
  is_hausdorff := krull_t2 K L,
  }
