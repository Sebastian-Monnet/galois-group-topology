import field_theory.galois
import algebra.group.basic
import ring_theory.tensor_product
import topology.algebra.filter_basis
import order.filter.bases 
import data.finset.basic 
import data.set.finite 
import data.polynomial.eval 

open_locale classical


-- Adjoin roots
noncomputable def root_finset {K : Type*} [field K] (p : polynomial K) (L : Type*) [field L] 
[algebra K L] : finset L := 
(p.map (algebra_map K L)).roots.to_finset

lemma root_finset_def {K : Type*} [field K] (p : polynomial K) (L : Type*) [field L] [algebra K L] 
{x : L}: x ∈ root_finset p L ↔ x ∈ (p.map (algebra_map K L)).roots.to_finset :=
begin
  refl,
end

lemma root_eval_zero {K : Type*} [field K] {p : polynomial K} {L : Type*} [field L] [algebra K L] 
{x : L} (hx : x ∈ root_finset p L) (hp : p.monic) :
polynomial.eval₂ (algebra_map K L) x p = 0 :=
begin
  rw root_finset_def at hx,
  rw multiset.mem_to_finset at hx,
  rw polynomial.mem_roots at hx,
  {
    unfold polynomial.is_root at hx,
    rw polynomial.eval₂_eq_eval_map,
    exact hx,
  },
  {
    exact polynomial.map_monic_ne_zero (hp),
  },
end

noncomputable def min_polys {K E : Type*} [field K] [field E] [algebra K E] 
(h_findim : finite_dimensional K E) : finset (polynomial K) :=
finset.univ.image (minpoly K ∘ (finite_dimensional.fin_basis K E))


noncomputable def prod_min_polys {K E : Type*} [field K] [field E] [algebra K E] 
(h_findim : finite_dimensional K E) : polynomial K := 
finset.prod (min_polys h_findim) id

lemma prod_min_polys_monic {K E : Type*} [field K] [field E] [algebra K E] 
(h_findim : finite_dimensional K E) : 
(prod_min_polys h_findim).monic :=
begin
   refine polynomial.monic_prod_of_monic (min_polys h_findim) id _,
   intros p hp,
   unfold min_polys at hp,
   rw finset.mem_image at hp,
   cases hp with i hp,
   cases hp with hi hp, 
   rw ← hp,
   apply minpoly.monic,
   let v : E := (finite_dimensional.fin_basis K E) i,
   change is_integral K v,
   refine is_integral_of_mem_of_fg (⊤ : subalgebra K E) h_findim.out (v : E) _,
    simp,
end


noncomputable def force_noncomputable {α : Sort*} (a : α) : α :=
  function.const _ a (classical.choice ⟨a⟩)


noncomputable def adj_roots {K L : Type} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
intermediate_field K L :=
force_noncomputable
intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L)


lemma adj_roots_def {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
adj_roots h_findim = 
intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L) :=
rfl 

lemma adj_finset_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L] (S : finset L)  
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

lemma adj_roots_fin_dim {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} 
(h_findim : finite_dimensional K E) : finite_dimensional K (adj_roots h_findim) := 
begin
  let p := prod_min_polys h_findim,
  let S := root_finset p L,
  change finite_dimensional K (intermediate_field.adjoin K ↑S),
  refine adj_finset_finite_dimensional S _,
  intros x hx,
  use p,
  refine ⟨prod_min_polys_monic h_findim, root_eval_zero hx _⟩, 
  exact prod_min_polys_monic h_findim,
end

/--lemma adjoin_basis {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} 
(h_findim : finite_dimensional K E) : 
E = intermediate_field.adjoin K (finset.univ.image ((algebra_map ↥E L) ∘ 
finite_dimensional.fin_basis K E)) :=
begin
  let S := (finset.univ.image ((algebra_map ↥E L) ∘ finite_dimensional.fin_basis K E)),
  change E = intermediate_field.adjoin K S,
  sorry,
end-/



lemma im_in_adj_roots {K L : Type*} [field K] [field L] [algebra K L] {E : intermediate_field K L} 
(h_findim : finite_dimensional K E) (σ : L →ₐ[K] L) : 
intermediate_field.map E σ ≤ adj_roots h_findim := 
begin
  let S := (finset.univ.image ((algebra_map ↥E L) ∘ finite_dimensional.fin_basis K E)),
  have h_gen : E = intermediate_field.adjoin K S,
  {
    sorry,
  },
  have h_adjoin_swap : E.map σ = intermediate_field.adjoin K (σ.to_fun '' S),
  {
    rw h_gen,
    apply le_antisymm,
    {
      sorry,
    },
    {
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
    },
  },
  rw h_adjoin_swap,
  change intermediate_field.adjoin K (σ.to_fun '' S) ≤ 
  intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L),
  --rw intermediate_field.gi.gc,
  apply intermediate_field.gi.gc.monotone_l,
  intros x hx,
  cases hx with a hx,
  cases hx with ha hax,
  have h_root_of_minpoly : (polynomial.map (algebra_map K L) (minpoly K a)).is_root x,
  {
    --rw ← hax,
    simp,
    rw ← polynomial.eval₂_eq_eval_map,
    rw ← hax,
    change polynomial.eval₂ (algebra_map K L) (σ a) (minpoly K a) = 0,
    rw ← polynomial.alg_hom_eval₂_algebra_map,
    have h : function.injective (coe_fn σ),
    {
      
    },
  },
  have h_root_of_prod : (polynomial.map (algebra_map K L) (prod_min_polys h_findim)).is_root x,
  {
    sorry,
  },
  unfold root_finset,
  simp,
  rw polynomial.mem_roots,
  exact h_root_of_prod,
  exact polynomial.map_monic_ne_zero (prod_min_polys_monic h_findim),
  --change (polynomial.map (algebra_map K L) (prod_min_polys h_findim)).is_root x,
end
-- end adjoin roots 



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
  sorry,
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
      change σ (g (σ⁻¹ x)) = x,
      have h1 : σ⁻¹ x ∈ N,
      {
        let alg_hom : L →ₐ[K] L := σ.symm,
        have h_contain : intermediate_field.map E alg_hom ≤ N,
        {
          exact im_in_adj_roots hE σ.symm,
        },
        apply h_contain,
        change σ.symm x ∈ E.map alg_hom, 
        change alg_hom x ∈ E.map alg_hom,
        use x,
        split,
        simp,
        refl,
      },
      have h2 : g (σ⁻¹ x) = σ⁻¹ x,
      {
        rw subgroup.mem_carrier at hg,
        rw mem_fixing_subgroup_iff at hg,
        specialize hg (σ⁻¹ x),
        exact hg h1,
      },
      {
        rw h2,
        change σ(σ.symm x) = x,
        simp,
      },
    },
  end
}

