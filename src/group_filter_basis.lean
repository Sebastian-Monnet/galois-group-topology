import tactic
import field_theory.galois
import data.set.basic
import algebra.group.basic
import ring_theory.tensor_product
import topology.algebra.filter_basis
import order.filter.bases 
import linear_algebra.finite_dimensional
import data.finset.basic 
import data.set.finite 

open_locale classical


-- Adjoin roots
noncomputable def min_polys {K E : Type*} [field K] [field E] [algebra K E] 
(h_findim : finite_dimensional K E) : finset (polynomial K) :=
finset.univ.image (minpoly K ∘ (finite_dimensional.fin_basis K E))

def adj_roots {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) : intermediate_field K L := 
intermediate_field.adjoin K (polynomial.root_set (finset.prod (min_polys h_findim) (polynomial.map_ring_hom (algebra_map K E))) L)

lemma adj_finset_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L] (S : finset L)  (h_int : ∀ (x : L), x ∈ S → is_integral K x) : 
finite_dimensional K (intermediate_field.adjoin K (coe S : set L)) :=
begin
  refine intermediate_field.induction_on_adjoin_finset (S) (λ (E : intermediate_field K L), finite_dimensional K E) _ _,
  {
    have temp : (⊥ : intermediate_field K L) = (⊥ : intermediate_field K L) := rfl,
    rw ← intermediate_field.finrank_eq_one_iff at temp,
    refine finite_dimensional.finite_dimensional_of_finrank _,
    rw temp,
    simp,
  },
  {
    intros E x hx,
    dsimp,
    specialize h_int x hx,
    intro h,
    apply intermediate_field.adjoin.finite_dimensional,
  },
end


lemma adj_roots_fin_dim {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} (h_findim : finite_dimensional K E) : finite_dimensional K (adj_roots h_findim) := 
begin
  sorry, 
end

lemma im_in_adj_roots {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} (h_findim : finite_dimensional K E) (σ : L →ₐ[K] L) : intermediate_field.map E σ ≤ adj_roots h_findim := 
begin
  sorry,
end
-- end adjoin roots 



/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finite_exts (K : Type*) [field K] (L : Type*) [field L] [algebra K L] : set (intermediate_field K L) :=
{E | finite_dimensional K E}

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite -/
def fixed_by_finite (K L : Type*) [field K] [field L] [algebra K L]: set (subgroup (L ≃ₐ[K] L)) :=
intermediate_field.fixing_subgroup '' (finite_exts K L)


 
lemma finite_dimensional_sup {K L: Type*} [field K] [field L] [algebra K L] (E1 E2 : intermediate_field K L) : finite_dimensional K E1 ∧ finite_dimensional K E2 → finite_dimensional K ↥(E1 ⊔ E2) :=
begin
  -- will just wait for Browning's version to get into mathlib
  sorry,
end



lemma mem_fixing_subgroup_iff {K L : Type*} [field K] [field L] [algebra K L] (E : intermediate_field K L) (σ : (L ≃ₐ[K] L)): σ ∈ E.fixing_subgroup ↔  ∀ (x : L), x ∈ E → σ x = x :=
--⟨ λ hσ x hx, hσ ⟨x, hx⟩, λ h ⟨x, hx⟩, h x hx⟩
begin
  split,
  {
    intros hσ x hx,
    --let y : E := ⟨ x, hx ⟩,
    exact hσ ⟨x, hx⟩,
  },
  {rintro h ⟨x, hx⟩,
  refine h x hx},
end



lemma inclusion_reversing {K L : Type*} [field K] [field L] [algebra K L] (E1 E2 : intermediate_field K L) : E1 ≤ E2 → E2.fixing_subgroup ≤ E1.fixing_subgroup :=
begin
  intro h12,
  intros σ hσ,
  rw mem_fixing_subgroup_iff,
  intros x hx,
  specialize h12 hx,
  let y : E2 := ⟨ x, h12 ⟩,
  have hy : σ y = y,
  apply hσ,
  exact hy,
end


def gal_basis (K L : Type*) [field K] [field L] [algebra K L] : filter_basis (L ≃ₐ[K] L) :=
{ sets := subgroup.carrier '' (fixed_by_finite K L),
  nonempty :=
  begin
      apply set.nonempty.image,
      apply set.nonempty.image,
      use ⊥,
      refine finite_dimensional_of_dim_eq_one _,
      simp,
  end,
  inter_sets :=
  begin
    rintros X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩,
    let E := E1 ⊔ E2,
    use (intermediate_field.fixing_subgroup E).carrier,
    split,
    {
      use E.fixing_subgroup,
      refine ⟨_, rfl⟩,
      use E,
      refine ⟨_, rfl⟩,
      apply finite_dimensional_sup E1 E2,
      exact ⟨h_E1, h_E2⟩,
    },
    {
      rw set.subset_inter_iff,
      split,
      {
        apply inclusion_reversing,
        simp [le_Sup],
      },
      {
        apply inclusion_reversing,
        simp [le_Sup],
      },
    },
  end
}

lemma mem_gal_basis_iff (K L : Type*) [field K] [field L] [algebra K L] (U : set (L ≃ₐ[K] L)) : U ∈ gal_basis K L ↔ U ∈ subgroup.carrier '' (fixed_by_finite K L) :=
begin
  refl, 
end


def gal_group_basis (K L : Type*) [field K] [field L] [algebra K L] : group_filter_basis (L ≃ₐ[K] L) :=
{ to_filter_basis := gal_basis K L,
  one' := 
  begin
    rintros U ⟨H, hH, rfl⟩,
    exact H.one_mem',
  end,
  mul' := 
  begin
    intros U hU,
    use U,
    refine ⟨hU, _⟩,
    rcases hU with ⟨H, hH, rfl⟩,
    rintros x ⟨a, b, haH, hbH, rfl⟩,
    exact H.mul_mem' haH hbH,
  end,
  inv' := 
  begin
    intros U hU,
    use U,
    refine ⟨hU, _⟩,
    dsimp,
    rcases hU with ⟨H, hH, rfl⟩,
    exact H.inv_mem',
  end,
  conj' := 
  begin
    rintros σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩,
    let N : intermediate_field K L := adj_roots hE,
    use N.fixing_subgroup.carrier, 
    split, 
    {
      use N.fixing_subgroup,
      refine ⟨_, rfl⟩,
      use N,
      exact ⟨adj_roots_fin_dim hE, rfl⟩,
    },
    {
      intros g hg,
      change σ * g * σ⁻¹ ∈ E.fixing_subgroup, 
      intro x,
      sorry,
    },
  end
}

