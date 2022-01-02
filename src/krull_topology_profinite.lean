import field_theory.galois 
import group_filter_basis
import topology.category.CompHaus.default
import order.filter.ultrafilter

open group_filter_basis

open_locale classical


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

lemma fixing_subgroup_is_open {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
is_open (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
begin
  sorry, 
end

lemma coset_open {G : Type*} [group G] [topological_space G] [topological_group G]
{U : set G} (x : G) (h : is_open U) :
is_open (left_coset x U) :=
begin 
  let f := homeomorph.mul_left x,
  have h' : left_coset x U = f '' U := rfl,
  rw h',
  rw homeomorph.is_open_image,
  exact h,
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
  let h_findim : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (h_int x),
  let H := E.fixing_subgroup,
  have h_basis : H.carrier ∈ gal_group_basis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩,
  have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
  rw mem_nhds_iff at h_nhd,
  rcases h_nhd with ⟨W, hWH, hW_open, hW_1⟩,
  refine ⟨left_coset f W, left_coset g W, ⟨coset_open f hW_open, coset_open g hW_open,
  ⟨1, hW_1, by apply mul_one⟩, ⟨1, hW_1, by apply mul_one⟩, _⟩⟩,
  by_contra h_nonempty,
  change left_coset f W ∩ left_coset g W ≠ ∅ at h_nonempty,
  rw set.ne_empty_iff_nonempty at h_nonempty,
  rcases h_nonempty with ⟨σ, ⟨⟨w1, hw1, hfw1⟩, ⟨w2, hw2, hgw2⟩⟩⟩,
  rw ← hgw2 at hfw1,
  rename hfw1 h,
  rw eq_inv_mul_iff_mul_eq.symm at h,
  rw ← mul_assoc at h,
  rw mul_inv_eq_iff_eq_mul.symm at h,
  have h_in_H : w1 * w2⁻¹ ∈ H := H.mul_mem' (hWH hw1) (H.inv_mem' (hWH hw2)),
  rw h at h_in_H,
  change φ ∈ E.fixing_subgroup at h_in_H,
  rw mem_fixing_subgroup_iff at h_in_H,
  specialize h_in_H x,
  have hxE : x ∈ E,
  {
    apply intermediate_field.subset_adjoin,
    apply set.mem_singleton,
  },
  exact hφx (h_in_H hxE),
end}


section finite_stuff

variables {K E L : Type*} [field K] [field E] [algebra K E] [field L] [algebra K L]
  [finite_dimensional K E]

noncomputable instance foo {E : Type*} {X : set E} (hX : X.finite) {L : Type*}
  (F : E → multiset L) : fintype (Π x : X, {l : L // l ∈ F x}) :=
by { classical, letI : fintype X := set.finite.fintype hX, exact pi.fintype}

variable (K)

noncomputable def aux_fun1 : E → multiset L :=
λ e, ((minpoly K e).map (algebra_map K L)).roots

lemma minpoly.ne_zero' (e : E) : minpoly K e ≠ 0 :=
minpoly.ne_zero $ is_integral_of_noetherian (is_noetherian.iff_fg.2 infer_instance) _

variable (E)

def basis_set: set E :=
set.range (finite_dimensional.fin_basis K E : _ → E)

variable (L)

-- function from Hom_K(E,L) to pi type Π (x : basis), roots of min poly of x
def aux_fun2 (φ : E →ₐ[K] L) (x : basis_set K E) :
  {l : L // l ∈ (aux_fun1 K x.1 : multiset L)} :=
⟨φ x, begin
  unfold aux_fun1,
  rw [polynomial.mem_roots_map (minpoly.ne_zero' K x.val),
    ← polynomial.alg_hom_eval₂_algebra_map, ← φ.map_zero],
  exact congr_arg φ (minpoly.aeval K (x : E)),
end⟩

lemma aux_inj : function.injective (aux_fun2 K E L) :=
begin
  intros f g h,
  suffices : (f : E →ₗ[K] L) = g,
  { rw linear_map.ext_iff at this,
    ext x, exact this x },
  rw function.funext_iff at h,
  apply linear_map.ext_on (finite_dimensional.fin_basis K E).span_eq,
  rintro e he,
  have := (h ⟨e, he⟩),
  apply_fun subtype.val at this,
  exact this,
end

noncomputable def its_finite : fintype (E →ₐ[K] L) :=
let n := finite_dimensional.finrank K E in
begin
  let B : basis (fin n) K E := finite_dimensional.fin_basis K E,
  let X := set.range (B : fin n → E),
  have hX : X.finite := set.finite_range ⇑B,
  refine @fintype.of_injective _ _
    (foo hX (λ e, ((minpoly K e).map (algebra_map K L)).roots)) _ (aux_inj K E L),
end

end finite_stuff

lemma preimage_univ (X Y : Type*) (f : X → Y) :
f⁻¹' (set.univ) = (set.univ) :=
begin 
  ext,
  refine ⟨λ h, set.mem_univ x, _⟩,
  intro h,
  change f x ∈ set.univ,
  exact set.mem_univ (f x), 
end


noncomputable def sigma_fun {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (h_findim : finite_dimensional K E)
(f : ultrafilter (L ≃ₐ[K] L)) (x : L) (hxE : x ∈ E):
L :=
begin
  let p : (L ≃ₐ[K] L) → (E →ₐ[K] L) := λ σ, alg_hom.restrict_domain E σ.to_alg_hom,
  let f' := f.map p,
  let s : set (E →ₐ[K] L ):= set.univ,
  have h_fin : s.finite,
  {
    haveI h_fintype := its_finite K E L,
    exact set.finite_univ,
  },
  have h_sf' : s ∈ f',
  {
    have h_sf : set.univ ∈ f' := f'.to_filter.univ_sets,
    rw ultrafilter.mem_map at h_sf,
    rw set.preimage_univ at h_sf,
    exact f.to_filter.univ_sets,
  },
  have h_principal := ultrafilter.eq_principal_of_finite_mem h_fin h_sf',
  choose ϕ hϕ using h_principal,
  cases hϕ with hϕs hϕf',
  exact ϕ ⟨x, hxE⟩,
end

def sigma_equiv {K L : Type*} [field K] [field L] [algebra K L]
(f : ultrafilter (L ≃ₐ[K] L)) :
L ≃ₐ[K] L :=
begin
  sorry,
end

def res {K L : Type*} [field K] [field L] [algebra K L] (E : intermediate_field K L):
(L ≃ₐ[K] L) → (E →ₐ[K] L) :=
λ f, f.to_alg_hom.comp E.val

lemma res_eq_map {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L}
(σ : L ≃ₐ[K] L) (x : E) : 
σ x = (res E σ) x :=
begin
  unfold res,
  simp,
end

example (G : Type*) [group G] (S : set G) (x y : G) (h : x ∈ left_coset y S) :
y⁻¹ * x ∈ S :=
begin
  rw mem_left_coset_iff at h, 
  exact h,
end

-- I know this is a terrible name
lemma inv_mul_alg_equiv_of_elem {K L : Type*} [field K] [field L] [algebra K L]
(x : L) (f g : L ≃ₐ[K] L)  :
(f⁻¹ * g) x = x ↔ g x = f x :=
begin
   rw alg_equiv.mul_apply,
   split,
   {
    intro h,
    have h' := congr_arg f h,
    rw ← alg_equiv.mul_apply at h',
    rw mul_right_inv at h',
    exact h',
   },
   {
    intro h,
    have h' := congr_arg f.symm h,
    rw alg_equiv.symm_apply_apply at h',
    exact h',
   },
end



example (X Y : Type*) (f: X → Y) (s : set X) (t : set Y) :
s ⊆ f⁻¹' t ↔f '' s ⊆ t :=
begin
  refine set.image_subset_iff.symm, 
end 

lemma top_group_map_nhds_eq {G : Type*} [group G] [topological_space G]
[topological_group G] (g x : G) :
filter.map (λ y, g * y) (nhds x) = nhds (g * x) :=
begin
  ext,
  split,
  {
    intro h,
    rw filter.mem_map at h,
    rw mem_nhds_iff at h,
    rcases h with ⟨U, h_subset, h_open, hxU⟩,
    rw mem_nhds_iff,
    use left_coset g U,
    split,
    {
      rw ← set.image_subset_iff at h_subset,
      exact h_subset,
    },
    refine ⟨_, ⟨x, ⟨hxU, rfl⟩⟩⟩,
    apply is_open_map_mul_left g,
    exact h_open,
  },
  {
    intro h,
    rw mem_nhds_iff at h,
    rcases h with ⟨U, h_subset, h_open, hgxU⟩,
    rw [filter.mem_map, mem_nhds_iff],
    use left_coset g⁻¹ U,
    split,
    {
      rw ← set.image_subset_iff,
      have h : (λ (y : G), g * y) '' left_coset g⁻¹ U = U,
      {
        ext a,
        refine ⟨_, λ ha, ⟨g⁻¹ * a, ⟨a, ha, rfl⟩, by simp⟩⟩,
        rintro ⟨b, ⟨c, hcU, hcb⟩, hba⟩,
        change g⁻¹ * c = b at hcb,
        change g * b = a at hba,
        rw [← hcb, ← mul_assoc, mul_right_inv, one_mul] at hba,
        rw ← hba,
        exact hcU,
      },
      rw h,
      exact h_subset,
    },
    split,
    {
      apply is_open_map_mul_left g⁻¹,
      exact h_open,
    },
    {
      use g * x,
      exact ⟨hgxU, by simp⟩,
    },
  },
end


lemma sigma_is_limit {K L : Type*} [field K] [field L] [algebra K L] 
(f : ultrafilter (L ≃ₐ[K] L)) (h_le_princ : ↑f ≤ filter.principal 
 (set.univ : set (L ≃ₐ[K] L))) :
(f : filter (L ≃ₐ[K] L)) ≤ nhds (sigma_equiv f) :=
begin 
  let σ := sigma_equiv f,
  intros A hA,
  have hA_coset : left_coset σ⁻¹ A ∈ nhds (1 : L ≃ₐ[K] L),
  {
    have h_sigma_1 : σ = σ * 1 := by simp,
    change A ∈ nhds σ at hA,
    rw h_sigma_1 at hA,
    rw ← top_group_map_nhds_eq σ 1 at hA,
    rw filter.mem_map at hA,
    have h : left_coset σ⁻¹ A = (λ y, σ * y)⁻¹' A,
    {
      ext,
      split,
      {
        rintro ⟨a, ha, hax⟩,
        simp [hax.symm, ha],
      },
      {
        intro hx,
        rw set.mem_preimage at hx,
        rw mem_left_coset_iff,
        rw inv_inv,
        exact hx,
      },
    },
    rw h,
    exact hA,
  },
  have hA_coset_cont_H : ∃ (E : intermediate_field K L), finite_dimensional K E 
  ∧ E.fixing_subgroup.carrier ⊆ left_coset σ⁻¹ A := sorry,
  cases hA_coset_cont_H with E hE,
  cases hE with h_findim hEA,
  have hEA' : left_coset σ E.fixing_subgroup ⊆ A := sorry,
  let p : (L ≃ₐ[K] L) → (E →ₐ[K] L) := λ σ, (σ.to_alg_hom.comp E.val),
  have h_principal : f.map p = pure (p σ) := sorry,

  -- here the point is that the left-coset is precisely the preimage under 
  -- p of {σ|_E}
  have h_small_set : left_coset σ E.fixing_subgroup ∈ f,
  {
    have h : {p σ} ∈ (pure (p σ) : ultrafilter (E →ₐ[K] L)) := set.mem_singleton (p σ),
    rw ← h_principal at h,
    rw ultrafilter.mem_map at h,
    have h_preim : p⁻¹' {p σ} = left_coset σ E.fixing_subgroup, 
    {
      ext g,
      split,
      {
        intro hg,
        rw set.mem_preimage at hg,
        rw set.mem_singleton_iff at hg,
        rw mem_left_coset_iff,
        intro x,
        have h_g_on_x : g x = (p g) x := res_eq_map g x,
        have h_σ_on_x : σ x = (p σ) x := res_eq_map σ x,
        rw inv_mul_alg_equiv_of_elem,
        rw [h_g_on_x, h_σ_on_x],
        rw hg,
      },
      {
        intro hg,
        rw set.mem_preimage,
        rw set.mem_singleton_iff,
        ext,
        have h_g_on_x : g x = (p g) x := res_eq_map g x,
        have h_σ_on_x : σ x = (p σ) x := res_eq_map σ x,
        rw [← h_g_on_x, ← h_σ_on_x],
        rw ← inv_mul_alg_equiv_of_elem,
        have h_fix : σ⁻¹ * g ∈ E.fixing_subgroup,
        {
          rw mem_left_coset_iff at hg,
          exact hg,
        },
        specialize h_fix x,
        rw h_fix,
      },
    },
    rw h_preim at h,
    exact h,
  },
  exact f.to_filter.sets_of_superset h_small_set hEA',  
end


lemma krull_compact (K L : Type*) [field K] [field L] [algebra K L] :
is_compact (set.univ : set (L ≃ₐ[K] L)) :=
begin
  sorry,
end


def krull_topology_hausdorff (K L : Type*) [field K] [field L] [algebra K L]
(h_int : ∀ (x : L), is_integral K x):
CompHaus :=
{ to_Top := Top.of (L ≃ₐ[K] L),
  is_compact := {
    compact_univ := krull_compact K L},
  is_hausdorff := krull_t2 K L h_int,
}
