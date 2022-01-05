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


lemma nonempty_interior_of_open_subset {X : Type*} [topological_space X] {S U : set X}
(hUS : U ⊆ S) (hU_open : is_open U) (hU_nonempty : U.nonempty):
(interior S).nonempty :=
begin
  cases hU_nonempty with x hxU,
  exact ⟨x, (interior_maximal hUS hU_open) hxU⟩,
end

def subgroup_of_interior_of_subgroup {G : Type*} [group G] [topological_space G] 
[topological_group G] {H : subgroup G} (h1_int : (1 : G) ∈ interior H.carrier) :
subgroup G :=
{ carrier := interior H.carrier,
  one_mem' := 
  begin 
    exact h1_int,
  end,
  mul_mem' :=
  begin 
    intros a b ha hb,
    let m : G → G := λ x, a * x,
    have h_sub_H : m '' interior(H.carrier) ⊆ H.carrier,
    {
      intros y hy,
      cases hy with p hp,
      cases hp with hp hapy,
      change a * p = y at hapy,
      rw ← hapy,
      exact H.mul_mem' (interior_subset ha) (interior_subset hp),
    },
    have h_open : is_open (m '' interior(H.carrier)),
    {
      apply is_open_map_mul_left,
      exact is_open_interior,
    },
    have h : m '' (interior H.carrier) ⊆ interior H.carrier,
    {
      rw subset_interior_iff_subset_of_open,
      {
        exact h_sub_H,
      },
      {
        exact h_open,
      },
    },
    apply h,
    use b,
    split,
    {
      exact hb,
    },
    {
      refl,
    },
  end,
  inv_mem' :=
  begin 
    intros x hx,
    let i : G → G := λ x, x⁻¹,
    have h_int_open : is_open (interior H.carrier) := is_open_interior,
    have h_open : is_open (i '' (interior H.carrier)),
  end
  }

lemma subgroup_of_interior_of_subgroup_open {G : Type*} [group G] [topological_space G] 
[topological_group G] {H : subgroup G} (h1_int : (1 : G) ∈ interior H.carrier) :
is_open (subgroup_of_interior_of_subgroup h1_int).carrier :=
begin
  change is_open (interior H.carrier),
  exact is_open_interior,
end

lemma open_subgroup_of_open_subgroup {G : Type*} [group G] [topological_space G] 
[topological_group G] (H1 H2 : subgroup G) (h_le : H1 ≤ H2) (h_open : is_open H1.carrier) :
is_open H2.carrier :=
begin 
  have h_eq_int : interior H2.carrier = H2.carrier,
  {
    apply le_antisymm,
    {
      exact interior_subset,
    },
    {
      intros x hx,
      use left_coset x H1,
      split,
      {
        split,
        {
          apply is_open_map_mul_left,
          exact h_open,
        },
        {
          intros a ha,
          cases ha with y ha,
          cases ha with hy haxy,
          change x * y = a at haxy,
          rw ← haxy,
          exact H2.mul_mem' hx (h_le hy),
        },
      },
      {
        use 1,
        exact ⟨H1.one_mem', by simp⟩,
      },
    },
  },
  rw ← h_eq_int,
  exact is_open_interior,
end

lemma open_subgroup_of_nonempty_interior {G : Type*} [group G] [topological_space G] 
[topological_group G] {H : subgroup G} (h_1_int : (1 : G) ∈ interior H.carrier) :
is_open H.carrier :=
open_subgroup_of_open_subgroup (subgroup_of_interior_of_subgroup h_1_int)
  H interior_subset (subgroup_of_interior_of_subgroup_open h_1_int)


lemma fixing_subgroup_is_open {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
is_open (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
begin
  have h_basis : E.fixing_subgroup.carrier ∈ (gal_group_basis K L) :=
   ⟨E.fixing_subgroup, ⟨E, h_findim, rfl⟩, rfl⟩,
  have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
  rw mem_nhds_iff at h_nhd,
  cases h_nhd with U h_nhd,
  cases h_nhd with hU_le h_nhd,
  cases h_nhd with hU_open h1U,
  have h_1_int : (1 : (L ≃ₐ[K] L)) ∈ interior E.fixing_subgroup.carrier := 
  ⟨U, ⟨hU_open, hU_le⟩, h1U⟩,
  exact open_subgroup_of_nonempty_interior h_1_int,
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

open set

lemma ultrafilter.eq_principal_of_fintype (X : Type*) [fintype X]
  (f : ultrafilter X) : ∃ x : X, (f : filter X) = pure x :=
let ⟨x, hx1, (hx2 : (f : filter X) = pure x)⟩ :=
  ultrafilter.eq_principal_of_finite_mem (finite_univ : (univ : set X).finite)
  (filter.univ_mem) in
⟨x, hx2⟩

-- here's a short def
noncomputable def alg_hom_of_finite_dimensional_of_ultrafilter
  {K L : Type*} [field K] [field L] [algebra K L]
  {E : intermediate_field K L} (h_findim : finite_dimensional K E)
  (f : ultrafilter (L ≃ₐ[K] L)) : E →ₐ[K] L :=
classical.some
  (@ultrafilter.eq_principal_of_fintype (E →ₐ[K] L) (its_finite K E L) 
  (f.map (λ σ, σ.to_alg_hom.comp (intermediate_field.val E))))

-- f.map ((L ≃ₐ[K] L) → (E →ₐ[K] L)) is generated by 
-- alg_hom_of_finite_dimensional_of_ultrafilter_spec h_findim f 
lemma alg_hom_of_finite_dimensional_of_ultrafilter_spec {K L : Type*} [field K] [field L] [algebra K L]
  {E : intermediate_field K L} (h_findim : finite_dimensional K E)
  (f : ultrafilter (L ≃ₐ[K] L)) :

(f.map (λ σ : L ≃ₐ[K] L, σ.to_alg_hom.comp (intermediate_field.val E)) : filter (E →ₐ[K] L)) =
  pure (alg_hom_of_finite_dimensional_of_ultrafilter h_findim f) :=

classical.some_spec
  (@ultrafilter.eq_principal_of_fintype (E →ₐ[K] L) (its_finite K E L) 
  (f.map (λ σ, σ.to_alg_hom.comp (intermediate_field.val E))))

def intermediate_field.inclusion {K L : Type*} [field K] [field L] [algebra K L]
  {E F : intermediate_field K L} (hEF : E ≤ F):
  E →ₐ[K] F :=
{ to_fun := set.inclusion hEF,
  map_one' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  commutes' := λ _, rfl }

lemma inclusion_eq_identity {K L : Type*} [field K] [field L] [algebra K L]
  {E F : intermediate_field K L} (hEF : E ≤ F) (x : E) :
  F.val ((intermediate_field.inclusion hEF) x) = E.val x :=
  begin 
    refl,
  end

lemma inclusion_commutes_with_val {K L : Type*} [field K] [field L] [algebra K L]
  {E F : intermediate_field K L} (hEF : E ≤ F) :
  F.val ∘ (intermediate_field.inclusion hEF) = E.val :=
begin
  refl,
end

lemma val_inj {K L : Type*} [field K] [field L] [algebra K L]
  {E : intermediate_field K L} :
  function.injective E.val :=
begin
  intros x y hxy,
  exact subtype.ext hxy,
end

lemma inclusion_commutes_with_mk {K L : Type*} [field K] [field L] [algebra K L] {E F : intermediate_field K L}
(hEF : E ≤ F) {x : L} (hx : x ∈ E) :
(intermediate_field.inclusion hEF) ⟨x, hx⟩ = ⟨x, hEF hx⟩ :=
begin
  apply val_inj,
  rw inclusion_eq_identity,
  simp,
end



lemma ultrafilter.map_map {X Y Z: Type*} (m : X → Y) (n : Y → Z) (f : ultrafilter X) :
(f.map m).map n = f.map(n ∘ m) :=
begin
  ext,
  split,
  {
    intro hs,
    rw [ultrafilter.mem_map, set.preimage_comp, ← ultrafilter.mem_map, ← ultrafilter.mem_map],
    exact hs,
  },
  {
    intro hs,
    rw [ultrafilter.mem_map, ultrafilter.mem_map, ← set.preimage_comp, ← ultrafilter.mem_map],
    exact hs,
  },
end

lemma ultrafilter.map_pure {X Y : Type*} (x : X) (m : X → Y):
(pure x : ultrafilter X).map m = pure (m x)  :=
begin 
  refl,
end

lemma alg_hom_of_finite_dimensional_of_ultrafilter_functor {K L : Type*} [field K] [field L] [algebra K L]
  {E : intermediate_field K L} (hE : finite_dimensional K E)
  (f : ultrafilter (L ≃ₐ[K] L)) {F : intermediate_field K L} (hF : finite_dimensional K F) (hEF : E ≤ F)
  :
  alg_hom_of_finite_dimensional_of_ultrafilter hE f = 
  (alg_hom_of_finite_dimensional_of_ultrafilter hF f).comp (intermediate_field.inclusion hEF) :=
  begin
    set p_E :=  (λ σ : L ≃ₐ[K] L, σ.to_alg_hom.comp (intermediate_field.val E)) with p_E_def,
    set p_F :=  (λ σ : L ≃ₐ[K] L, σ.to_alg_hom.comp (intermediate_field.val F)) with p_F_def,
    set σ_E := alg_hom_of_finite_dimensional_of_ultrafilter hE f with σ_E_def,
    set σ_F := alg_hom_of_finite_dimensional_of_ultrafilter hF f with σ_F_def,
    have hσ_E := alg_hom_of_finite_dimensional_of_ultrafilter_spec hE f,
    rw [← p_E_def, ← σ_E_def] at hσ_E,
    have hσ_F := alg_hom_of_finite_dimensional_of_ultrafilter_spec hF f,
    rw [← p_F_def, ← σ_F_def] at hσ_F,
    set res : (F →ₐ[K] L) → (E →ₐ[K] L) := (λ ϕ, ϕ.comp (intermediate_field.inclusion hEF))
    with res_def,
    have h_pF_pE_res : res ∘ p_F = p_E := rfl,
    have h_maps_commute : ((f.map p_F).map res : filter (E →ₐ[K] L)) = f.map p_E,
    {
      rw ultrafilter.map_map,
      rw h_pF_pE_res,
    },
    have hEf  := alg_hom_of_finite_dimensional_of_ultrafilter_spec hE f,
    rw [← σ_E_def, ← p_E_def] at hEf,
    have hFf := alg_hom_of_finite_dimensional_of_ultrafilter_spec hF f,
    rw [← σ_F_def, ← p_F_def] at hFf,
    have hFf' : (ultrafilter.map p_F f) = (pure σ_F : ultrafilter (F →ₐ[K] L)),
    {
      exact ultrafilter.coe_inj.mp hFf,
    },
    rw hEf at h_maps_commute,
    rw hFf' at h_maps_commute,
    rw ultrafilter.map_pure at h_maps_commute,
    have h := filter.pure_injective h_maps_commute,
    rw res_def at h,
    dsimp at h,
    exact h.symm,
  end

noncomputable def function_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) :
(L → L) :=
λ x, (alg_hom_of_finite_dimensional_of_ultrafilter 
(intermediate_field.adjoin.finite_dimensional (h_int x)) f) 
(⟨x, intermediate_field.mem_adjoin_simple_self K x⟩)


lemma function_of_ultrafilter_spec {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) {E : intermediate_field K L}
(hE : finite_dimensional K E) (x : E) :
(function_of_ultrafilter h_int f) x = (alg_hom_of_finite_dimensional_of_ultrafilter hE f) x :=
begin
   have h_le : intermediate_field.adjoin K {(x : L)} ≤ E,
   {
     apply intermediate_field.gc.l_le,
     simp only [set_like.coe_mem, set_like.mem_coe, set.singleton_subset_iff, set.le_eq_subset],
   },
   have h_Kx : finite_dimensional K (intermediate_field.adjoin K {(x : L)}) :=
   intermediate_field.adjoin.finite_dimensional (h_int x),
   let h_functor := alg_hom_of_finite_dimensional_of_ultrafilter_functor h_Kx f hE h_le,
   have h : (function_of_ultrafilter h_int f) x = 
   (alg_hom_of_finite_dimensional_of_ultrafilter h_Kx f) ⟨x, 
   intermediate_field.mem_adjoin_simple_self K x⟩ := rfl,
   rw [h, h_functor],
   let x_in_Kx : intermediate_field.adjoin K {(x : L)} := ⟨(x : L), 
   intermediate_field.mem_adjoin_simple_self K (x : L)⟩,
   have h' : (intermediate_field.inclusion h_le) x_in_Kx = x := by
     simp [inclusion_commutes_with_mk h_le (intermediate_field.mem_adjoin_simple_self K (x : L))],
   simp [h'],
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
      exact ⟨g * x, hgxU, by simp⟩,
    },
  },
end

example (G : Type*) [group G] (x y z : G):
x⁻¹ * y = z ↔ y = x * z := by refine inv_mul_eq_iff_eq_mul

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
    rw [h_sigma_1, ← top_group_map_nhds_eq σ 1, filter.mem_map] at hA,
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
        rw [mem_left_coset_iff, inv_inv],
        exact hx,
      },
    },
    rw h,
    exact hA,
  },
  have hA_coset_cont_H : ∃ (E : intermediate_field K L), finite_dimensional K E 
  ∧ E.fixing_subgroup.carrier ⊆ left_coset σ⁻¹ A,
  {
    rw nhds_one_eq at hA_coset,
    rw filter_basis.mem_filter_iff at hA_coset,
    rcases hA_coset with ⟨H_set, hH, hA_coset⟩,
    change H_set ∈ gal_basis K L at hH,
    rw mem_gal_basis_iff at hH,
    rcases hH with ⟨H, ⟨E, hE, hHE⟩, hHH_set⟩,
    refine ⟨E, hE, _⟩,
    rw [hHE, hHH_set],
    exact hA_coset,    
  },
  rcases hA_coset_cont_H with ⟨E, h_findim, hEA⟩,
  have hEA' : left_coset σ E.fixing_subgroup ⊆ A,
  {
    intros x hx,
    rcases hx with ⟨y, hy, hyx⟩,
    change σ * y = x at hyx,
    specialize hEA hy,
    rcases hEA with ⟨a, ha, hay⟩,
    change σ⁻¹ * a = y at hay,
    rw inv_mul_eq_iff_eq_mul at hay,
    rw [← hyx, ← hay],
    exact ha,
  },
  let p : (L ≃ₐ[K] L) → (E →ₐ[K] L) := λ σ, (σ.to_alg_hom.comp E.val),
  have h_principal : f.map p = pure (p σ),
  {
    sorry,
  },

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
