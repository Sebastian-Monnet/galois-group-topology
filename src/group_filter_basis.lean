import field_theory.galois
import topology.algebra.filter_basis
import normal_closure

open_locale classical



lemma intermediate_field.map_mono {K L M : Type*} [field K] [field L] [field M]
  [algebra K L] [algebra K M] {E1 E2 : intermediate_field K L}
  (σ : L ≃ₐ[K] M) (h12 : E1 ≤ E2) : 
E1.map σ.to_alg_hom ≤ E2.map σ.to_alg_hom :=
set.image_subset σ h12 

lemma intermediate_field.map_id {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} : 
E.map (alg_hom.id K L) = E :=
set_like.coe_injective $ set.image_id _



-- I switched the order -- more complicated thing on the left of an ↔
-- you don't use this anywhere anyway
lemma int_field_map_iso {K L : Type*} [field K] [field L] [algebra K L] 
{E1 E2 : intermediate_field K L} (σ : L ≃ₐ[K] L) :
E1.map σ.to_alg_hom ≤ E2.map σ.to_alg_hom ↔ E1 ≤ E2 :=
σ.to_equiv.image_subset E1 E2

-- you don't use this
lemma algebra_map_map_inv {K L : Type*} [field K] [field L] [algebra K L] 
(E : intermediate_field K L) (σ : L ≃ₐ[K] L) : 
(E.to_subalgebra.map σ.to_alg_hom).map σ.symm.to_alg_hom = E.to_subalgebra :=
by simp [subalgebra.map_map]

-- special case of intermediate_field.adjoin_map
lemma adjoin_map_le_map_adjoin {K L : Type*} [field K] [field L] [algebra K L] (S : set L) 
(σ : L ≃ₐ[K] L) : 
(intermediate_field.adjoin K S).map σ.to_alg_hom ≤ 
intermediate_field.adjoin K (σ '' S) :=
le_of_eq (intermediate_field.adjoin_map K S σ)

-- this is adjoin_map again
lemma adjoin_map_eq_map_adjoin {K L : Type*} [field K] [field L] [algebra K L] (S : set L) 
(σ : L ≃ₐ[K] L) : 
(intermediate_field.adjoin K S).map σ.to_alg_hom =
intermediate_field.adjoin K (σ.to_fun '' S) :=
intermediate_field.adjoin_map K S σ

-- more complex thing on the left. You never use this and we have it already.
lemma eq_subalg_iff_eq_submodule {R : Type*} {A : Type*} [comm_semiring R] [semiring A] 
[algebra R A] (E1 E2 : subalgebra R A):
E1.to_submodule = E2.to_submodule ↔ E1 = E2 := 
subalgebra.to_submodule_inj

-- you don't use this either
lemma span_subalg_of_span_submod {R A : Type*} [comm_semiring R] [semiring A] 
[algebra R A] (s : set A) (h : submodule.span R s = ⊤) : 
algebra.adjoin R s = ⊤ :=
begin
  refine subalgebra.to_submodule_injective (_ : _ = ⊤),
  rw [← top_le_iff, ← h],
  exact algebra.span_le_adjoin R s,
end

-- this and the next few lemmas would make some nice PR's
@[simps] def ring_equiv.subsemiring_map {R S : Type*} [non_assoc_semiring R] [non_assoc_semiring S] 
 (e : R ≃+* S) (s : subsemiring R) :
  s ≃+* s.map e.to_ring_hom :=
{ ..e.to_add_equiv.add_submonoid_map s.to_add_submonoid,
  ..e.to_mul_equiv.submonoid_map s.to_submonoid }

@[simps] def ring_equiv.subring_map {R S : Type*} [ring R] [ring S] (e : R ≃+* S) (s : subring R) :
  s ≃+* s.map e.to_ring_hom :=
e.subsemiring_map s.to_subsemiring

@[simps] def alg_equiv.subalgebra_map {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] (e : A ≃ₐ[R] B) (S : subalgebra R A) :
  S ≃ₐ[R] (S.map e.to_alg_hom) :=
{ commutes' := λ r, by { ext, simp },
  ..e.to_ring_equiv.subsemiring_map S.to_subsemiring }

@[simps] def alg_equiv.intermediate_field_map {K L M : Type*} [field K] [field L] [field M]
  [algebra K L] [algebra K M] (e : L ≃ₐ[K] M) (E : intermediate_field K L) :
  E ≃ₐ[K] (E.map e.to_alg_hom) :=
e.subalgebra_map E.to_subalgebra


-- we've got this, really
lemma equiv_finite_dimensional {K L L' : Type*} [field K] [field L] [field L']
[algebra K L] [algebra K L'] (σ : L ≃ₐ[K] L') (h_findim : finite_dimensional K L) :
finite_dimensional K L' :=
linear_equiv.finite_dimensional σ.to_linear_equiv

lemma im_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (σ : L ≃ₐ[K] L) (h_findim : finite_dimensional K E): 
finite_dimensional K (E.map σ.to_alg_hom) :=
linear_equiv.finite_dimensional (alg_equiv.intermediate_field_map σ E).to_linear_equiv

/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finite_exts (K : Type*) [field K] (L : Type*) [field L] [algebra K L] : 
set (intermediate_field K L) :=
{E | finite_dimensional K E}

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite -/
def fixed_by_finite (K L : Type*) [field K] [field L] [algebra K L]: set (subgroup (L ≃ₐ[K] L)) :=
intermediate_field.fixing_subgroup '' (finite_exts K L)

lemma intermediate_field.finite_dimensional_bot (K L : Type*) [field K] 
  [field L] [algebra K L] : finite_dimensional K (⊥ : intermediate_field K L) :=
finite_dimensional_of_dim_eq_one intermediate_field.dim_bot 

lemma intermediate_field.fixing_subgroup.bot {K L : Type*} [field K] 
  [field L] [algebra K L] : 
  intermediate_field.fixing_subgroup (⊥ : intermediate_field K L) = ⊤ :=
begin
  ext f,
  refine ⟨λ _, subgroup.mem_top _, λ _, _⟩,
  rintro ⟨x, hx⟩,
  rw intermediate_field.mem_bot at hx,
  rcases hx with ⟨y, rfl⟩,
  exact f.commutes y,
end

lemma top_fixed_by_finite {K L : Type*} [field K] [field L] [algebra K L] : 
  ⊤ ∈ fixed_by_finite K L :=
⟨⊥, intermediate_field.finite_dimensional_bot K L, intermediate_field.fixing_subgroup.bot⟩

-- we have this, it doesn't need to be here
lemma finite_dimensional_sup {K L: Type*} [field K] [field L] [algebra K L] 
  (E1 E2 : intermediate_field K L) (h1 : finite_dimensional K E1)
  (h2 : finite_dimensional K E2) : finite_dimensional K ↥(E1 ⊔ E2) :=
by exactI intermediate_field.finite_dimensional_sup E1 E2

lemma mem_fixing_subgroup_iff {K L : Type*} [field K] [field L] [algebra K L] 
(E : intermediate_field K L) (σ : (L ≃ₐ[K] L)): σ ∈ E.fixing_subgroup ↔  
∀ (x : L), x ∈ E → σ x = x :=
⟨λ hσ x hx, hσ ⟨x, hx⟩, λ h ⟨x, hx⟩, h x hx⟩

lemma intermediate_field.fixing_subgroup.antimono {K L : Type*} [field K] [field L] [algebra K L] 
{E1 E2 : intermediate_field K L} (h12 : E1 ≤ E2) : E2.fixing_subgroup ≤ E1.fixing_subgroup :=
begin
  rintro σ hσ ⟨x, hx⟩,
  exact hσ ⟨x, h12 hx⟩,
end

def gal_basis (K L : Type*) [field K] [field L] [algebra K L] : filter_basis (L ≃ₐ[K] L) :=
{ sets := subgroup.carrier '' (fixed_by_finite K L),
  nonempty := ⟨⊤, ⊤, top_fixed_by_finite, rfl⟩,
  inter_sets :=
  begin
    rintros X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩,
    use (intermediate_field.fixing_subgroup (E1 ⊔ E2)).carrier,
    refine ⟨⟨_, ⟨_, finite_dimensional_sup E1 E2 h_E1 h_E2, rfl⟩, rfl⟩, _⟩,
    rw set.subset_inter_iff,
    exact ⟨intermediate_field.fixing_subgroup.antimono le_sup_left,
      intermediate_field.fixing_subgroup.antimono le_sup_right⟩,
  end
}

lemma mem_gal_basis_iff (K L : Type*) [field K] [field L] [algebra K L] 
(U : set (L ≃ₐ[K] L)) : U ∈ gal_basis K L ↔ U ∈ subgroup.carrier '' (fixed_by_finite K L) :=
iff.rfl

-- we have this
lemma inv_comp {K L : Type*} [field K] [field L] [algebra K L] (σ : L ≃ₐ[K] L) (x : L) :
σ(σ⁻¹(x)) = x :=
alg_equiv.apply_symm_apply σ x

def gal_group_basis (K L : Type*) [field K] [field L] [algebra K L] : 
group_filter_basis (L ≃ₐ[K] L) :=
{ to_filter_basis := gal_basis K L,
  one' := λ U ⟨H, hH, h2⟩, h2 ▸ H.one_mem,
  mul' := λ U hU, ⟨U, hU, begin
    rcases hU with ⟨H, hH, rfl⟩,
    rintros x ⟨a, b, haH, hbH, rfl⟩,
    exact H.mul_mem haH hbH,
  end⟩,
  inv' := λ U hU, ⟨U, hU, begin
    rcases hU with ⟨H, hH, rfl⟩,
    exact H.inv_mem',
  end⟩,
  conj' := 
  begin
    rintros σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩,
    let F : intermediate_field K L := E.map (σ.symm.to_alg_hom),
    refine ⟨F.fixing_subgroup.carrier, ⟨⟨F.fixing_subgroup, ⟨F, 
      im_finite_dimensional σ.symm hE, rfl⟩, rfl⟩, λ g hg, _⟩⟩,
    change σ * g * σ⁻¹ ∈ E.fixing_subgroup,
    rw mem_fixing_subgroup_iff,
    intros x hx,
    change σ(g(σ⁻¹ x)) = x,
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by {dsimp, rw ← alg_equiv.inv_fun_eq_symm, refl }⟩,
    have h_g_fix : g (σ⁻¹ x) = (σ⁻¹ x),
    { rw [subgroup.mem_carrier, mem_fixing_subgroup_iff F g] at hg,
      exact hg (σ⁻¹ x) h_in_F,
    },
    rw h_g_fix,
    rw inv_comp,
  end
}


@[instance]
def krull_topology (K L : Type*) [field K] [field L] [algebra K L] :
topological_space (L ≃ₐ[K] L) :=
group_filter_basis.topology (gal_group_basis K L)


def krull_topological_group (K L : Type*) [field K] [field L] [algebra K L] :
topological_group (L ≃ₐ[K] L) :=
group_filter_basis.is_topological_group (gal_group_basis K L)


