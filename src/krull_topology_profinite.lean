import field_theory.galois 
import field_theory.krull_topology
import topology.category.CompHaus.default
import order.filter.ultrafilter
import topology.algebra.open_subgroup
import topology.category.Profinite.default 


open_locale classical

/-!
# Krull topology profinite

Let `L/K` be a normal algebraic field extension. We show that the Krull topology on `L ≃ₐ[K] L` is 
profinite, in the sense that it is a compact, Hausdorff, and totally disconnected topological space. 

## Main definitions

- `krull_topology_t2 K L h_int`. For an integral field extension `L/K`,`krull_topology_t2 K L h_int` 
  is a term of type `t2_space(L ≃ₐ[K] L)`. The existence of the such a term implies that the Krull topology is 
  Hausdorff. Here `h_int` is a term of type `∀ (x : L), is_integral K x`. That is, `h_int` is 
  a proof that the extension `L/K` is integral. 

- `alg_hom_of_finite_dimensional_of_ultrafilter h_findim f`. Let `L/E/K` be a tower of fields and let 
  `h_findim : finite_dimensional K L` be a proof that `E/K` is finite-dimensional. Let 
  `f : ultrafilter(L ≃ₐ[K] L)`. The restriction map `(L ≃ₐ[K] L) → (E →ₐ[K] L)` pushes `f`
  forward to an ultrafilter `f*` on `(E →ₐ[K] L)`. Since `(E →ₐ[K] L)` is a finite set, any 
  ultrafilter on it is principal. Therefore, `f*` is a principal ultrafilter, and 
  `alg_hom_of_finite_dimensional_ultrafilter h_findim f` generates it. 

- `function_of_ultrafilter h_int f`. Let `L/E/K` be a tower of fields, with `E/K` finite Let `f` be 
  an ultrafilter on `L ≃ₐ[K] L`, and let `h_int : ∀ (x : L), is_integral K x`. Write 
  `σ_E` for `alg_hom_of_finite_dimensional_of_ultrafilter h_findim f`, where 
  `h_findim : finite_dimensional K E`. Each `σ_E` is a map `E → L`, and we would like to 
  glue these maps together to obtain a map `L → L`. This glued map is 
  `function_of_ultrafilter h_int f`. 

- `alg_hom_of_ultrafilter h_int f`. Let `L/K` be an integral field extension and let 
  `h_int : ∀ (x : L), is_integral K x`. Let `f` be an ultrafilter on `L ≃ₐ[K] L`. Then 
  `alg_hom_of_ultrafilter h_int f` is a term of `L →ₐ[K] L` whose underlying map is 
  `function_of_ultrafilter h_int f`. 

- `equiv_of_ultrafilter h_int f`. Let `L/K` be an integral field extension and let 
  `h_int : ∀ (x : L), is_integral K x`. Let `f` be an ultrafilter on `L ≃ₐ[K] L`. Then 
  `equiv_of_ultrafilter h_int f`is a term of `L ≃ₐ[K] L` whose underlying map is
  `function_of_ultrafilter h_int f`. 

- `krull_topology_comphaus h_int h_splits`. Let `L/K` be an integral, normal field extension. Let 
  `h_int : ∀ (x : L), is_integral K x` and `h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) (minpoly K x)`. 
  That is, `h_int` is a proof that the extension is integral, and `h_splits` is a proof that it is normal. Then 
  `krull_topology_comphaus h_int h_splits` is a term of type `CompHaus` whose underlying topology is the Krull topology 
  on `L ≃ₐ[K] L`. 

- `krull_topology_totally_disconnected h_int`. Let `L/K` be an integral field extension. Let 
  `h_int : ∀ (x : L), is_integral K x`. Then `krull_topology_totally_disconnected h_int` is a term of type 
  `totally_disconnected_space (L ≃ₐ[K] L)`, whose underlying topology is the Krull topology. 

- `krull_topology_profinite h_int h_splits`. Let `L/K` be an integral, normal field extension. Let 
  `h_int : ∀ (x : L), is_integral K x` and `h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) (minpoly K x)`. 
  That is, `h_int` is a proof that the extension is integral, and `h_splits` is a proof that it is normal. Then 
  `krull_topology_profinite h_int h_splits` is a term of type `Profinite`, whose underlying topological space is the
  Krull topology on `L ≃ₐ[K] L`. 

## Main results

- `krull_topology_compact h_int h_splits`. If `L/K` be an integral, normal field extension, then 
  the Krull topology on `L ≃ₐ[K] L` is compact. 

-/

/-- If `f,g : L → L` are distinct `K`-algebra equivalences, then there is some `x ∈ L` with 
  `f(x) ≠ g(x)`. -/
lemma diff_equivs_have_diff_values {K L : Type*} [field K] [field L] [algebra K L]
{f g : L ≃ₐ[K] L} (h : f ≠ g) :
∃ (x : L), f x ≠ g x :=
begin
  contrapose! h,
  exact alg_equiv.ext h,
end

open_locale topological_space filter



/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
lemma open_subgroup_of_nonempty_interior {G : Type*} [group G] [topological_space G]
[topological_group G] {H : subgroup G} (h_1_int : (1 : G) ∈ interior (H : set G)) :
is_open (H : set G) :=
begin
  have h : 𝓝 1 ≤ 𝓟 (H : set G) :=
    nhds_le_of_le h_1_int (is_open_interior) (filter.principal_mono.2 interior_subset),
  rw is_open_iff_nhds,
  intros g hg,
  rw (show 𝓝 g = filter.map ⇑(homeomorph.mul_left g) (𝓝 1), by simp),
  convert filter.map_mono h,
  simp only [homeomorph.coe_mul_left, filter.map_principal, set.image_mul_left, filter.principal_eq_iff_eq],
  ext,
  simp [H.mul_mem_cancel_left (H.inv_mem hg)],
end

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of 
  `L ≃ₐ[K] L`. -/
lemma fixing_subgroup_is_open {K L : Type*} [field K] [field L] [algebra K L] 
(E : intermediate_field K L) [finite_dimensional K E] :
is_open (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
begin
  have h_basis : E.fixing_subgroup.carrier ∈ (gal_group_basis K L) :=
   ⟨E.fixing_subgroup, ⟨E, _inst_4, rfl⟩, rfl⟩,
  have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
  rw mem_nhds_iff at h_nhd,
  rcases h_nhd with ⟨U, hU_le, hU_open, h1U⟩,
  exact open_subgroup_of_nonempty_interior ⟨U, ⟨hU_open, hU_le⟩, h1U⟩,
end

section a 
variables (F α : Sort*) (β : α → Sort*)
variables {F α β} [i : fun_like F α β]
include i 

lemma fun_like.exists_ne {f g : F} (h : f ≠ g) : ∃ x, f x ≠ g x :=
not_forall.mp $ mt (fun_like.ext _ _) h
end a

/-- If `L/K` is an algebraic extension, then the Krull topology on `L ≃ₐ[K] L` is Hausdorff. -/
lemma krull_topology_t2 (K L : Type*) [field K] [field L] [algebra K L] (h_int : 
algebra.is_integral K L):
t2_space (L ≃ₐ[K] L)  :=
{ t2 := 
begin 
  intros f g hfg,
  let φ := f⁻¹ * g,
  have h : ∃(x : L), f x ≠ g x,
  {
    apply fun_like.exists_ne,
    exact hfg,
  },
  cases (fun_like.exists_ne hfg) with x hx,
  have hφx : φ x ≠ x,
  {
    --change f⁻¹(g x) ≠ x,
    apply ne_of_apply_ne f,
    change f (f.symm (g x)) ≠ f x,
    rw [alg_equiv.apply_symm_apply f (g x), ne_comm],
    exact hx,
  },
  let E : intermediate_field K L := intermediate_field.adjoin K {x},
  let h_findim : finite_dimensional K E := 
  intermediate_field.adjoin.finite_dimensional (h_int x),
  let H := E.fixing_subgroup,
  have h_basis : (H : set(L ≃ₐ[K] L)) ∈ gal_group_basis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩,
  have h_nhd := group_filter_basis.mem_nhds_one (gal_group_basis K L) h_basis,
  rw mem_nhds_iff at h_nhd,
  rcases h_nhd with ⟨W, hWH, hW_open, hW_1⟩,
  refine ⟨left_coset f W, left_coset g W, ⟨is_open.left_coset hW_open f, is_open.left_coset hW_open g,
  ⟨1, hW_1, by apply mul_one⟩, ⟨1, hW_1, by apply mul_one⟩, _⟩⟩,
  by_contra h_nonempty,
  change left_coset f W ∩ left_coset g W ≠ ∅ at h_nonempty,
  rw set.ne_empty_iff_nonempty at h_nonempty,
  rcases h_nonempty with ⟨σ, ⟨⟨w1, hw1, hfw1⟩, ⟨w2, hw2, hgw2⟩⟩⟩,
  rw ← hgw2 at hfw1,
  rename hfw1 h,
  rw [eq_inv_mul_iff_mul_eq.symm, ← mul_assoc, mul_inv_eq_iff_eq_mul.symm] at h,
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

section totally_disconnected

/-- Let `X` be a topological space, and suppose that for all distinct `x,y ∈ X`, there
  is some clopen set `U` such that `x ∈ U` and `y ∉ U`. Then `X` is totally disconnected. -/
lemma is_totally_disconnected_of_clopen_set {X : Type*} [topological_space X] 
(h_exists_clopen : ∀ {x y : X} (h_diff : x ≠ y), ∃ (U : set X) (h_clopen : is_clopen U), x ∈ U ∧ y ∉ U) :
is_totally_disconnected (set.univ : set X) :=
begin
  intros S _ hS,
  by_contra,
  unfold set.subsingleton at h,
  simp at h,
  rcases h with ⟨x, hx, y, hy, hxy⟩,
  specialize h_exists_clopen hxy,
  rcases h_exists_clopen with ⟨U, h_clopen, hxU, hyU⟩,
  let V := set.compl U,
  have hV_open : is_open V,
  {
    rw ← is_closed_compl_iff,
    change is_closed U.compl.compl,
    simp,
    exact h_clopen.2,
  },
  specialize hS U V h_clopen.1 hV_open (λ a ha, em (a ∈ U)) ⟨x, hx, hxU⟩ ⟨y, hy, hyU⟩,
  have hUV : U ∩ V = ∅,
  {
   change U ∩ U.compl = ∅,
   simp, 
  },
  rw hUV at hS,
  simp at hS,
  exact hS,
end

/-- Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ L ≃ₐ[K] L` is
  closed. -/
lemma fixing_subgroup_is_closed {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
is_closed (E.fixing_subgroup : set (L ≃ₐ[K] L)) :=
begin
  let h_open : open_subgroup (L ≃ₐ[K] L) := 
  { to_subgroup := E.fixing_subgroup,
    is_open' := fixing_subgroup_is_open E,
  },
  exact open_subgroup.is_closed h_open,
end

/-- If `L/K` is an algebraic field extension, then the Krull topology on `L ≃ₐ[K] L` is 
  totally disconnected. -/
lemma krull_totally_disconnected {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : ∀ (x : L), is_integral K x) :
is_totally_disconnected (set.univ : set (L ≃ₐ[K] L)) :=
begin
  apply is_totally_disconnected_of_clopen_set,
  intros σ τ h_diff,
  have hστ : σ⁻¹ * τ ≠ 1,  
  {
    simp [inv_mul_eq_one],
    exact h_diff,
  },
  cases (diff_equivs_have_diff_values hστ) with x hx,
  change (σ⁻¹ * τ) x ≠ x at hx,
  let E := intermediate_field.adjoin K ({x} : set L),
  refine ⟨left_coset σ E.fixing_subgroup, 
  ⟨is_open.left_coset (fixing_subgroup_is_open (intermediate_field.adjoin.finite_dimensional (h_int x))) σ,
    is_closed.left_coset (fixing_subgroup_is_closed (intermediate_field.adjoin.finite_dimensional (h_int x))) σ⟩, 
    ⟨1, E.fixing_subgroup.one_mem', by simp⟩, 
    _⟩,
  rw mem_left_coset_iff,
  change ¬ σ⁻¹ * τ ∈ E.fixing_subgroup,
  rw mem_fixing_subgroup_iff E (σ⁻¹ * τ),
  simp,
  exact ⟨x, intermediate_field.mem_adjoin_simple_self K x, hx⟩,  
end

end totally_disconnected




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

universe u

-- here's a short def
noncomputable def alg_hom_of_finite_dimensional_of_ultrafilter
  {K : Type*} {L : Type u} [field K] [field L] [algebra K L]
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
      rw [ultrafilter.map_map, h_pF_pE_res],
    },
    have hEf  := alg_hom_of_finite_dimensional_of_ultrafilter_spec hE f,
    rw [← σ_E_def, ← p_E_def] at hEf,
    have hFf := alg_hom_of_finite_dimensional_of_ultrafilter_spec hF f,
    rw [← σ_F_def, ← p_F_def] at hFf,
    have hFf' : (ultrafilter.map p_F f) = (pure σ_F : ultrafilter (F →ₐ[K] L)),
    {
      exact ultrafilter.coe_inj.mp hFf,
    },
    rw [hEf, hFf', ultrafilter.map_pure] at h_maps_commute,
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

lemma adj_finset_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L]
(S : finset L)  
(h_int : ∀ (x : L), x ∈ S → is_integral K x) : 
finite_dimensional K (intermediate_field.adjoin K (coe S : set L)) :=
begin
  refine intermediate_field.induction_on_adjoin_finset (S) (λ (E : intermediate_field K L), 
  finite_dimensional K E) _ _,
  {
    have temp : (⊥ : intermediate_field K L) = (⊥ : intermediate_field K L) := rfl,
    rw ← intermediate_field.finrank_eq_one_iff at temp,
    refine finite_dimensional.finite_dimensional_of_finrank _,
    rw temp,
    exact zero_lt_one,
  },
  {
    intros E x hx,
    specialize h_int x hx,
    introI h,
    haveI h2 : finite_dimensional ↥E (↥E)⟮x⟯,
    {
      apply intermediate_field.adjoin.finite_dimensional,
      exact is_integral_of_is_scalar_tower x h_int,
    },
    change finite_dimensional K ↥(↥E)⟮x⟯,
    exact finite_dimensional.trans K ↥E ↥(↥E)⟮x⟯,
  },
end

noncomputable def alg_hom_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) :
(L →ₐ[K] L) :=
{ to_fun := function_of_ultrafilter h_int f,
  map_one' := 
  begin
    have h_findim_bot : finite_dimensional K (⊥ : intermediate_field K L) := 
    intermediate_field.finite_dimensional_bot K L,
    have h_one_bot : (1 : L) ∈ (⊥: intermediate_field K L) := (⊥ : intermediate_field K L).one_mem,
    have h := function_of_ultrafilter_spec h_int f h_findim_bot (1 : (⊥ : intermediate_field K L)),
    simp at h,
    exact h,
  end,
  map_mul' := 
  begin
    intros x y,
    let E := intermediate_field.adjoin K ({x, y} : set L),
    have h_sub : {x, y} ⊆ E.carrier := intermediate_field.gc.le_u_l {x, y},
    have hxE : x ∈ E := h_sub (mem_insert x {y}),
    have hyE : y ∈ E,
    {
      apply h_sub,
      simp only [set.mem_insert_iff, set.mem_singleton, or_true],
    },
    have hxyE : x * y ∈ E := E.mul_mem' hxE hyE, 
    let S := ({x, y} : finset L),
    have h_S_int : ∀ (x : L), x ∈ S → is_integral K x :=
    λ a ha, h_int a,
    have hE := adj_finset_finite_dimensional S h_S_int,
    have h_S_coes : (S : set L) = {x, y},
    {
      simp only [finset.coe_insert, finset.coe_singleton, eq_self_iff_true],
    },
    rw h_S_coes at hE,
    change finite_dimensional K E at hE,
    have h : function_of_ultrafilter h_int f x = function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) := rfl,
    change function_of_ultrafilter h_int f (⟨x * y, hxyE⟩ : E) = 
    function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) * 
    function_of_ultrafilter h_int f (⟨y, hyE⟩ : E),
    rw [function_of_ultrafilter_spec h_int f hE ⟨x, hxE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨y, hyE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨x * y, hxyE⟩],
    have h2 : (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨x, hxE⟩ *
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨y, hyE⟩ = 
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) (⟨x, hxE⟩ * ⟨y, hyE⟩),
    {
      simp only [mul_eq_mul_left_iff, true_or, eq_self_iff_true, map_mul],
    },
    rw h2,
    refl,
  end,
  map_zero' :=
  begin
    have h_findim_bot : finite_dimensional K (⊥ : intermediate_field K L) := 
    intermediate_field.finite_dimensional_bot K L,
    have h_zero_bot : (0 : L) ∈ (⊥: intermediate_field K L) := (⊥ : intermediate_field K L).zero_mem,
    have h := function_of_ultrafilter_spec h_int f h_findim_bot (0 : (⊥ : intermediate_field K L)),
    simp at h,
    exact h,
  end,
  map_add' := 
  begin
    intros x y,
    let E := intermediate_field.adjoin K ({x, y} : set L),
    have h_sub : {x, y} ⊆ E.carrier := intermediate_field.gc.le_u_l {x, y},
    have hxE : x ∈ E := h_sub (mem_insert x {y}),
    have hyE : y ∈ E,
    {
      apply h_sub,
      simp only [set.mem_insert_iff, set.mem_singleton, or_true],
    },
    have hxyE : x + y ∈ E := E.add_mem' hxE hyE, 
    let S := ({x, y} : finset L),
    have h_S_int : ∀ (x : L), x ∈ S → is_integral K x :=
    λ a ha, h_int a,
    have hE := adj_finset_finite_dimensional S h_S_int,
    have h_S_coes : (S : set L) = {x, y},
    {
      simp only [finset.coe_insert, finset.coe_singleton, eq_self_iff_true],
    },
    rw h_S_coes at hE,
    change finite_dimensional K E at hE,
    have h : function_of_ultrafilter h_int f x = function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) := rfl,
    change function_of_ultrafilter h_int f (⟨x + y, hxyE⟩ : E) = 
    function_of_ultrafilter h_int f (⟨x, hxE⟩ : E) + 
    function_of_ultrafilter h_int f (⟨y, hyE⟩ : E),
    rw [function_of_ultrafilter_spec h_int f hE ⟨x, hxE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨y, hyE⟩,
    function_of_ultrafilter_spec h_int f hE ⟨x + y, hxyE⟩],
    have h2 : (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨x, hxE⟩ +
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) ⟨y, hyE⟩ = 
  (alg_hom_of_finite_dimensional_of_ultrafilter hE f) (⟨x, hxE⟩ + ⟨y, hyE⟩),
    {
      simp,
    },
    rw h2,
    refl, 
  end,
  commutes' := 
  begin
    intro r,
    let r' := (algebra_map K L) r,
    have h_findim_bot : finite_dimensional K (⊥ : intermediate_field K L) := 
    intermediate_field.finite_dimensional_bot K L,
    have h : r' ∈ (⊥ : intermediate_field K L) := (⊥ : intermediate_field K L).algebra_map_mem r,
    change function_of_ultrafilter h_int f (⟨r', h⟩ : (⊥ : intermediate_field K L)) = 
    (⟨r', h⟩ : (⊥ : intermediate_field K L)), 
    rw function_of_ultrafilter_spec h_int f h_findim_bot (⟨r', h⟩ : (⊥ : intermediate_field K L)),
    have h2 : (⟨r', h⟩ : (⊥ : intermediate_field K L)) = (algebra_map K (⊥ : intermediate_field K L)
    r) := rfl,
    rw h2,
    simp,
    refl,
  end,
  }





lemma alg_hom_of_ultrafilter_injective {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (f : ultrafilter (L ≃ₐ[K] L)) :
function.injective (alg_hom_of_ultrafilter h_int f) :=
begin 
  intros x y hxy,
  let E := intermediate_field.adjoin K ({x, y} : set L),
  let S := ({x, y} : finset L),
  have h_S_int : ∀ (x : L), x ∈ S → is_integral K x :=
  λ a ha, h_int a,
  have hE := adj_finset_finite_dimensional S h_S_int,
  have h_S_coes : (S : set L) = {x, y},
  {
    simp only [finset.coe_insert, finset.coe_singleton, eq_self_iff_true],
  },
  rw h_S_coes at hE,
  change finite_dimensional K E at hE,
  have h_sub : {x, y} ⊆ E.carrier := intermediate_field.gc.le_u_l {x, y},
  have hxE : x ∈ E := h_sub (mem_insert x {y}),
  have hyE : y ∈ E,
  {
    apply h_sub,
    simp only [set.mem_insert_iff, set.mem_singleton, or_true],
  },
  change (alg_hom_of_ultrafilter h_int f) (⟨x, hxE⟩ : E) = 
  (alg_hom_of_ultrafilter h_int f) (⟨y, hyE⟩ : E) at hxy,
  change (function_of_ultrafilter h_int f) (⟨x, hxE⟩ : E) = 
  (function_of_ultrafilter h_int f) (⟨y, hyE⟩ : E) at hxy,
  rw [function_of_ultrafilter_spec h_int f hE (⟨x, hxE⟩ : E), 
  function_of_ultrafilter_spec h_int f hE (⟨y, hyE⟩ : E)] at hxy,
  have h : (⟨x, hxE⟩ : E) = (⟨y, hyE⟩ : E),
  {
    exact ring_hom.injective (alg_hom_of_finite_dimensional_of_ultrafilter hE f).to_ring_hom hxy,
  },
  simp at h,
  exact h,
end

lemma eq_of_map_le {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L}
{f : L →ₐ[K] L} (h_findim : finite_dimensional K E) (h_map_le : E.map f ≤ E) :
E.map f = E :=
begin
  have hf_inj : function.injective f := ring_hom.injective f.to_ring_hom,
  haveI hE_submod_fin : finite_dimensional K E.to_subalgebra.to_submodule,
  {
    exact h_findim,
  },
  have h_finrank_eq : finite_dimensional.finrank K (E.map f) = 
  finite_dimensional.finrank K E,
  {
    exact (linear_equiv.finrank_eq (submodule.equiv_map_of_injective (f.to_linear_map) 
    hf_inj E.to_subalgebra.to_submodule)).symm,
  },
  have h_submod_le : (E.map f).to_subalgebra.to_submodule ≤ E.to_subalgebra.to_submodule := h_map_le,
  exact intermediate_field.to_subalgebra_eq_iff.mp (subalgebra.to_submodule_injective
  (finite_dimensional.eq_of_le_of_finrank_eq h_map_le h_finrank_eq)),
end

lemma alg_hom_of_ultrafilter_surjective {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) : 
function.surjective (alg_hom_of_ultrafilter h_int f) :=
begin 
  intro y,
  specialize h_splits y,
  let p := minpoly K y,
  let S := (p.map (algebra_map K L)).roots.to_finset,
  let E := intermediate_field.adjoin K (S : set L),
  have hE_findim : finite_dimensional K E := adj_finset_finite_dimensional S (λ x hx, h_int x),
  let σ := alg_hom_of_ultrafilter h_int f,
  have hσSS : σ '' S ⊆ S,
  {
    rintros x ⟨a, ha, hax⟩,
    rw ← hax,
    simp,
    rw polynomial.mem_roots,
    {
      rw [polynomial.is_root.def, ← polynomial.eval₂_eq_eval_map, ← polynomial.alg_hom_eval₂_algebra_map],
      have hσ0 : σ 0 = 0 := by simp,
      rw ← hσ0,
      apply congr_arg σ,
      simp at ha,
      rw polynomial.mem_roots at ha,
      {
        rw [polynomial.is_root.def, ← polynomial.eval₂_eq_eval_map] at ha,
        exact ha,
      },
      {
        exact polynomial.map_monic_ne_zero (minpoly.monic (h_int y)),
      },
    },
    exact polynomial.map_monic_ne_zero (minpoly.monic (h_int y)),
  },
  have hSE : (S : set L) ⊆ E := intermediate_field.gc.le_u_l (S : set L),
  have hσSE : σ '' S ⊆ E := set.subset.trans hσSS hSE,
  have h1 : E.map σ = intermediate_field.adjoin K (σ '' S) := intermediate_field.adjoin_map K S σ,
  have h2 : intermediate_field.adjoin K (σ '' S) ≤ E,
  {
    apply intermediate_field.gc.l_le,
    exact hσSE,
  },
  change ∃ (a : L), σ a = y,
  rw ← h1 at h2,
  have h3 := eq_of_map_le hE_findim h2,
  have hyE : y ∈ E,
  {
    have hyS : y ∈ S,
    {
      simp,
      rw polynomial.mem_roots,
      {
        rw [polynomial.is_root.def,
         ← polynomial.eval₂_eq_eval_map,
         ← polynomial.aeval_def],
        exact minpoly.aeval K y,
      },
      {
        exact polynomial.map_monic_ne_zero (minpoly.monic (h_int y)),
      },
    },
    exact hSE hyS,
  },
  rw ← h3 at hyE,
  rcases hyE with ⟨a, ha, hay⟩,
  exact ⟨a, hay⟩,
end

lemma alg_hom_of_ultrafilter_bijection {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
function.bijective (alg_hom_of_ultrafilter h_int f) :=
begin
  exact ⟨alg_hom_of_ultrafilter_injective h_int f, 
  alg_hom_of_ultrafilter_surjective h_int h_splits f⟩,
end

noncomputable def equiv_of_ultrafilter {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(L ≃ₐ[K] L) :=
alg_equiv.of_bijective (alg_hom_of_ultrafilter h_int f) (alg_hom_of_ultrafilter_bijection h_int h_splits f)

lemma equiv_of_ultrafilter_to_fun {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(equiv_of_ultrafilter h_int h_splits f).to_fun = function_of_ultrafilter h_int f :=
rfl 

lemma equiv_of_ultrafilter_to_alg_hom {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) :
(equiv_of_ultrafilter h_int h_splits f).to_alg_hom = alg_hom_of_ultrafilter h_int f :=
rfl 

lemma asdf {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) (f : ultrafilter (L ≃ₐ[K] L)) {E : intermediate_field K L} 
(h_findim : finite_dimensional K E) :
((equiv_of_ultrafilter h_int h_splits f).to_alg_hom.comp E.val) = 
alg_hom_of_finite_dimensional_of_ultrafilter h_findim f :=
begin
  ext,
  exact function_of_ultrafilter_spec h_int f h_findim x,
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
    rw [← alg_equiv.mul_apply, mul_right_inv] at h',
    exact h',
   },
   {
    intro h,
    have h' := congr_arg f.symm h,
    rw alg_equiv.symm_apply_apply at h',
    exact h',
   },
end



lemma top_group_map_nhds_eq {G : Type*} [group G] [topological_space G]
[topological_group G] (g x : G) :
filter.map (λ y, g * y) (nhds x) = nhds (g * x) :=
begin
  ext,
  split,
  {
    intro h,
    rw [filter.mem_map, mem_nhds_iff] at h,
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
    refine ⟨_, ⟨g * x, hgxU, by simp⟩⟩,
    apply is_open_map_mul_left g⁻¹,
    exact h_open,
    
  },
end


lemma sigma_is_limit {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) 
(f : ultrafilter (L ≃ₐ[K] L)) 
(h_le_princ : ↑f ≤ filter.principal 
 (set.univ : set (L ≃ₐ[K] L))) :
(f : filter (L ≃ₐ[K] L)) ≤ nhds (equiv_of_ultrafilter h_int h_splits f) :=
begin 
  let σ := equiv_of_ultrafilter h_int h_splits f,
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
    rw [group_filter_basis.nhds_one_eq, filter_basis.mem_filter_iff] at hA_coset,
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
    rintros x ⟨y, hy, hyx⟩,
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
    have h : p σ = alg_hom_of_finite_dimensional_of_ultrafilter h_findim f := 
    asdf h_int h_splits f h_findim,
    rw h,
    have h2 : ↑(ultrafilter.map p f) = pure (alg_hom_of_finite_dimensional_of_ultrafilter h_findim f) :=
    alg_hom_of_finite_dimensional_of_ultrafilter_spec h_findim f,
    ext,
    split,
    {
      intro hs,
      rw [← ultrafilter.mem_coe, h2] at hs,
      exact hs,
    },
    {
      intro hs,
      rw ultrafilter.mem_pure at hs,
      have h3 : s ∈ (pure (alg_hom_of_finite_dimensional_of_ultrafilter h_findim f) : filter (↥E →ₐ[K] L)),
      {
        rw filter.mem_pure,
        exact hs,
      },

      rw ← h2 at h3,
      rw ultrafilter.mem_coe at h3,
      exact h3,
    },
  },

  have h_small_set : left_coset σ E.fixing_subgroup ∈ f,
  {
    have h : {p σ} ∈ (pure (p σ) : ultrafilter (E →ₐ[K] L)) := set.mem_singleton (p σ),
    rw [← h_principal, ultrafilter.mem_map] at h,
    have h_preim : p⁻¹' {p σ} = left_coset σ E.fixing_subgroup, 
    {
      ext g,
      split,
      {
        intro hg,
        rw [set.mem_preimage, set.mem_singleton_iff] at hg,
        rw mem_left_coset_iff,
        intro x,
        have h_g_on_x : g x = (p g) x := res_eq_map g x,
        have h_σ_on_x : σ x = (p σ) x := res_eq_map σ x,
        change (σ⁻¹ * g) x = x,
        rw [inv_mul_alg_equiv_of_elem, h_g_on_x, h_σ_on_x, hg],
      },
      {
        intro hg,
        rw [set.mem_preimage, set.mem_singleton_iff],
        ext,
        have h_g_on_x : g x = (p g) x := res_eq_map g x,
        have h_σ_on_x : σ x = (p σ) x := res_eq_map σ x,
        rw [← h_g_on_x, ← h_σ_on_x, ← inv_mul_alg_equiv_of_elem],
        exact (mem_left_coset_iff σ).1 hg x,
      },
    },
    rw h_preim at h,
    exact h,
  },
  exact f.to_filter.sets_of_superset h_small_set hEA',  
end


lemma krull_topology_compact {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x))  :
is_compact (set.univ : set (L ≃ₐ[K] L)) := is_compact_iff_ultrafilter_le_nhds.2
  (λ f hf,  ⟨equiv_of_ultrafilter h_int h_splits f, 
  set.mem_univ (equiv_of_ultrafilter h_int h_splits f), 
  sigma_is_limit h_int h_splits f hf⟩)


def krull_topology_comphaus {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)):
CompHaus :=
{ to_Top := Top.of (L ≃ₐ[K] L),
  is_compact := {
    compact_univ := krull_topology_compact h_int h_splits},
  is_hausdorff := krull_topology_t2 K L h_int,
}

def krull_topology_totally_disconnected {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : ∀ (x : L), is_integral K x) : 
totally_disconnected_space (L ≃ₐ[K] L) :=
{ is_totally_disconnected_univ := krull_totally_disconnected h_int}

def krull_topology_profinite {K L : Type*} [field K] [field L] [algebra K L] 
(h_int : algebra.is_integral K L) (h_splits : ∀ (x : L), polynomial.splits (algebra_map K L) 
(minpoly K x)) :
Profinite := 
{ to_CompHaus := krull_topology_comphaus h_int h_splits,
  is_totally_disconnected := krull_topology_totally_disconnected h_int}
