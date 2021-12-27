import field_theory.galois
import topology.algebra.filter_basis

open_locale classical


noncomputable def force_noncomputable {α : Sort*} (a : α) : α :=
  function.const _ a (classical.choice ⟨a⟩)

-- probably delete
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


lemma intermediate_field_map_map {K L1 L2 L3 : Type*} [field K] [field L1] [algebra K L1]
[field L2] [algebra K L2] [field L3] [algebra K L3] 
(E : intermediate_field K L1) (f : L1 →ₐ[K] L2) (g : L2 →ₐ[K] L3) : 
(E.map f).map g = E.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

lemma map_adjoin_ge_adjoin_map {K L : Type*} [field K] [field L] [algebra K L] 
(S : finset L) 
(σ : L ≃ₐ[K] L) : 
(intermediate_field.adjoin K ↑S).map σ.to_alg_hom ≥ 
intermediate_field.adjoin K (σ.to_fun '' ↑S) :=
begin
  apply intermediate_field.gi.gc.l_le,
  intros x hx,
  cases hx with a hx,
  cases hx with ha hax,
  use a,
  split,
  {
    dsimp,
    apply intermediate_field.subset_adjoin,
    exact ha,
  },
  {
    exact hax,
  },
end

lemma int_field_map_mono {K L : Type*} [field K] [field L] [algebra K L] 
{E1 E2 : intermediate_field K L} (σ : L ≃ₐ[K] L) (h12 : E1 ≤ E2): 
E1.map σ.to_alg_hom ≤ E2.map σ.to_alg_hom :=
begin
  intros x hx,
  cases hx with a hx,
  cases hx with ha hax,
  use a, 
  simp,
  refine ⟨_, hax⟩,
  apply h12,
  exact ha,
end

lemma int_field_map_id {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} : 
E.map (alg_hom.id K L) = E :=
begin
  ext,
  split,
  {
    intro hx,
    cases hx with a hx,
    cases hx with ha hax,
    simp at hax,
    rw ← hax,
    exact ha, 
  },
  {
    intro hx,
    use x,
    simp,
    exact hx,
  },
end

lemma int_field_map_mono_other {K L : Type*} [field K] [field L] [algebra K L] 
{E1 E2 : intermediate_field K L} (σ : L ≃ₐ[K] L) 
(h12 : E1.map σ.to_alg_hom ≤ E2.map σ.to_alg_hom): 
E1 ≤ E2:=
begin
  have h_map_map := int_field_map_mono σ.symm h12,
  rw intermediate_field_map_map at h_map_map,
  rw intermediate_field_map_map at h_map_map,
  simp [int_field_map_id] at h_map_map,
  exact h_map_map,
end

lemma int_field_map_iso {K L : Type*} [field K] [field L] [algebra K L] 
{E1 E2 : intermediate_field K L} (σ : L ≃ₐ[K] L) :
E1 ≤ E2 ↔ E1.map σ.to_alg_hom ≤ E2.map σ.to_alg_hom :=
⟨int_field_map_mono σ, int_field_map_mono_other σ⟩ 

lemma algebra_map_map_inv {K L : Type*} [field K] [field L] [algebra K L] 
(E : intermediate_field K L) (σ : L ≃ₐ[K] L) : 
(E.to_subalgebra.map σ.to_alg_hom).map σ.symm.to_alg_hom = E.to_subalgebra :=
begin
  rw subalgebra.map_map E.to_subalgebra σ.symm.to_alg_hom σ.to_alg_hom,
  simp,
end

lemma adjoin_map_le_map_adjoin {K L : Type*} [field K] [field L] [algebra K L] (S : finset L) 
(σ : L ≃ₐ[K] L) : 
(intermediate_field.adjoin K ↑S).map σ.to_alg_hom ≤ 
intermediate_field.adjoin K (σ.to_fun '' ↑S) :=
begin
  have h := map_adjoin_ge_adjoin_map (σ.to_fun '' S).to_finset (σ.symm),
  have h2 : (σ.symm.to_fun '' ↑((σ.to_fun '' ↑S).to_finset)) = S,
  {
    ext,
    split,
    {
      intro hx,
      cases hx with b hx,
      cases hx with hb hbx,
      have h3 : ↑((σ.to_fun '' ↑S).to_finset) = σ.to_fun '' ↑S,
      {
        simp,
      },
      rw h3 at hb,
      cases hb with a hb,
      cases hb with ha hab,
      rw ← hab at hbx,
      simp at hbx,
      rw ← hbx,
      exact ha,
    },
    {
      intro hx,
      use σ x,
      split,
      {
        simp,
        use x,
        exact ⟨hx, rfl⟩,
      },
      {
        simp,
      },
    },
  },
  rw h2 at h,
  apply int_field_map_mono_other σ.symm, 
  rw ge_iff_le at h,
  rw intermediate_field_map_map,
  simp,
  rw int_field_map_id,
  dsimp,
  dsimp at h,
  have h3 : ↑((⇑σ '' ↑S).to_finset) = ⇑σ '' ↑S,
  {
    simp,
  },
  rw h3 at h,
  exact h,
end

lemma adjoin_map_eq_map_adjoin {K L : Type*} [field K] [field L] [algebra K L] (S : finset L) 
(σ : L ≃ₐ[K] L) : 
(intermediate_field.adjoin K ↑S).map σ.to_alg_hom =
intermediate_field.adjoin K (σ.to_fun '' ↑S) :=
begin
  apply le_antisymm,
  exact adjoin_map_le_map_adjoin S σ,
  apply intermediate_field.gi.gc.l_le,
  intros y hy,
  cases hy with x hx,
  cases hx with hx hxy,
  use x,
  split,
  dsimp,
  apply intermediate_field.subset_adjoin,
  exact hx,
  exact hxy,
end



lemma eq_subalg_iff_eq_submodule {R : Type*} {A : Type*} [comm_semiring R] [semiring A] 
[algebra R A] (E1 E2 : subalgebra R A):
E1 = E2 ↔ E1.to_submodule = E2.to_submodule :=
begin
  exact subalgebra.to_submodule_inj.symm,
end


lemma span_subalg_of_span_submod {R A : Type*} [comm_semiring R] [semiring A] 
[algebra R A] (s : set A) (h : submodule.span R s = ⊤) : 
algebra.adjoin R s = ⊤ :=
begin
  rw subalgebra.to_submodule_inj.symm,
  rw algebra.adjoin_eq_span,
  have h' : submodule.span R s ≤ submodule.span R (submonoid.closure s),
  {
    have h'' : s ≤ submonoid.closure s,
    {
      apply submonoid.subset_closure,
    },
    exact (submodule.gi R A).gc.monotone_l h'',
  },
  rw h at h',
  simp,
  exact eq_top_iff.mpr h',
end


lemma im_in_map {K L L' : Type*} [field K] [field L] [field L']
[algebra K L] [algebra K L'] (E : intermediate_field K L) (σ : L ≃ₐ[K] L') 
(x : E) :
σ x ∈ E.map σ.to_alg_hom :=
begin
  use x,
  simp,
end

lemma inv_im_in_subfield {K L L' : Type*} [field K] [field L] [field L']
[algebra K L] [algebra K L'] (E : intermediate_field K L) (σ : L ≃ₐ[K] L') 
(y : E.map σ.to_alg_hom) :
σ.symm y ∈ E :=
begin
  cases y with x hx,
  cases hx with a ha,
  cases ha with ha hax,
  simp,
  rw ← hax,
  simp,
  exact ha,
end


def intermediate_field_equiv_map {K L L' : Type*} [field K] [field L] [field L']
[algebra K L] [algebra K L'] (E : intermediate_field K L) (σ : L ≃ₐ[K] L') : 
E ≃ₐ[K] E.map σ.to_alg_hom :=
{ to_fun := λ x, ⟨σ x, im_in_map E σ x⟩,
  inv_fun := λ x, ⟨σ.symm x, inv_im_in_subfield E σ x⟩,
  left_inv := 
  begin
    intro x,
    simp, 
  end,
  right_inv :=
  begin
    intro x,
    simp,
  end,
  map_mul' := 
  begin
    intros x y,
    simp,
    refl, 
  end,
  map_add' :=
  begin
    intros x y,
    simp,
    refl, 
  end,
  commutes' :=
  begin
    intro x,
    ext,
    exact σ.commutes x,
  end
   }

lemma equiv_finite_dimensional {K L L' : Type*} [field K] [field L] [field L']
[algebra K L] [algebra K L'] (σ : L ≃ₐ[K] L') (h_findim : finite_dimensional K L) :
finite_dimensional K L' :=
begin
   exact linear_equiv.finite_dimensional σ.to_linear_equiv,
end

lemma im_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (σ : L ≃ₐ[K] L) (h_findim : finite_dimensional K E): 
finite_dimensional K (E.map σ.to_alg_hom) :=
linear_equiv.finite_dimensional (intermediate_field_equiv_map E σ).to_linear_equiv

/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finite_exts (K : Type*) [field K] (L : Type*) [field L] [algebra K L] : 
set (intermediate_field K L) :=
{E | finite_dimensional K E}

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite -/
def fixed_by_finite (K L : Type*) [field K] [field L] [algebra K L]: set (subgroup (L ≃ₐ[K] L)) :=
intermediate_field.fixing_subgroup '' (finite_exts K L)
 
lemma finite_dimensional_sup {K L: Type*} [field K] [field L] [algebra K L] 
(E1 E2 : intermediate_field K L) : finite_dimensional K E1 ∧ finite_dimensional K E2 
→ finite_dimensional K ↥(E1 ⊔ E2) :=
begin
  -- will just wait for Browning's version to get into mathlib
  rintro ⟨h1, h2⟩,
  resetI,
  exact intermediate_field.finite_dimensional_sup E1 E2,
end

lemma mem_fixing_subgroup_iff {K L : Type*} [field K] [field L] [algebra K L] 
(E : intermediate_field K L) (σ : (L ≃ₐ[K] L)): σ ∈ E.fixing_subgroup ↔  
∀ (x : L), x ∈ E → σ x = x :=
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

lemma inclusion_reversing {K L : Type*} [field K] [field L] [algebra K L] 
(E1 E2 : intermediate_field K L) : E1 ≤ E2 → E2.fixing_subgroup ≤ E1.fixing_subgroup :=
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

lemma mem_gal_basis_iff (K L : Type*) [field K] [field L] [algebra K L] 
(U : set (L ≃ₐ[K] L)) : U ∈ gal_basis K L ↔ U ∈ subgroup.carrier '' (fixed_by_finite K L) :=
begin
  refl, 
end

lemma inv_comp {K L : Type*} [field K] [field L] [algebra K L] (σ : L ≃ₐ[K] L) (x : L) :
σ(σ⁻¹(x)) = x :=
begin
  change σ (σ.symm x) = x,
  simp,
end

def gal_group_basis (K L : Type*) [field K] [field L] [algebra K L] : 
group_filter_basis (L ≃ₐ[K] L) :=
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
    let F : intermediate_field K L := E.map (σ.symm.to_alg_hom),
    use F.fixing_subgroup.carrier, 
    split,
    {
      rw mem_gal_basis_iff,
      use F.fixing_subgroup,
      split,
      {
        use F,
        refine ⟨_, rfl⟩,
        change finite_dimensional K F,
        refine im_finite_dimensional σ.symm hE,
      },
      refl,
    },
    intros g hg,
    rw set.mem_preimage,
    change σ * g * σ⁻¹ ∈ E.fixing_subgroup,
    rw mem_fixing_subgroup_iff,
    intros x hx,
    change σ(g(σ⁻¹ x)) = x,
    have h_in_F : σ⁻¹ x ∈ F,
    {
      use x,
      split,
      exact hx,
      dsimp,
      rw ← alg_equiv.inv_fun_eq_symm,
      refl,
    },
    {
      have h_g_fix : g (σ⁻¹ x) = (σ⁻¹ x),
      {
        simp at hg,
        rw mem_fixing_subgroup_iff F g at hg,
        specialize hg (σ⁻¹ x),
        exact hg h_in_F,
      },
      rw h_g_fix,
      rw inv_comp,
    },
  end
}


