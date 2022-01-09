import field_theory.galois

open_locale classical

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

lemma is_root_prod {K L : Type*} [field K] [field L] [algebra K L]
  (s : finset (polynomial K))  (x : L) :
  (polynomial.map (algebra_map K L) (finset.prod s id)).is_root x
   ↔ ∃ (p ∈ s), (polynomial.map (algebra_map K L) p).is_root x :=
begin
  simp,
  rw polynomial.map_prod,
  rw polynomial.eval_prod,
  rw finset.prod_eq_zero_iff,
  simp,
end

lemma root_prod_of_root_elem {K L : Type*} [field K] [field L] [algebra K L] 
{S : finset (polynomial K)} {x : L} {p : polynomial K} (hp : p ∈ S)
(h_root : (polynomial.map (algebra_map K L) p).is_root x) : 
(polynomial.map (algebra_map K L) (finset.prod S id)).is_root x :=
begin
  rw is_root_prod S x,
  use p,
  exact ⟨hp, h_root⟩,
end

noncomputable def force_noncomputable {α : Sort*} (a : α) : α :=
function.const _ a (classical.choice ⟨a⟩)

noncomputable def adj_roots {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
intermediate_field K L :=
force_noncomputable
intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L)


lemma adj_roots_def {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
adj_roots h_findim = 
intermediate_field.adjoin K (coe (root_finset (prod_min_polys h_findim) L) : set L) :=
rfl 

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



lemma subalg_le_gen_by_basis {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (h_findim : finite_dimensional K E)
(b := finite_dimensional.fin_basis K ↥E) :
E.to_subalgebra ≤ algebra.adjoin K (finset.image ((algebra_map ↥E L) ∘ b) finset.univ) :=
begin
   intros x hx,
   change x ∈ E at hx,
   let x' : ↥E := ⟨x, hx⟩,
   have hx' := basis.mem_span b x',
   apply algebra.span_le_adjoin K _,
   simp only [function.comp_app, finset.coe_image, finset.coe_univ, set.image_univ],
   rw set.range_comp,
   have h2 : ((E.val : E →ₗ[K] L) '' set.range ⇑b) = 
   (⇑(algebra_map ↥E L) '' set.range ⇑b),
   {
     refl,
   },
   rw ← h2,
   rw ← submodule.map_span (E.val : E →ₗ[K] L) (set.range ⇑b),
   use x',
   split,
   {
     exact hx',
   },
   {
     refl,
   },
end


lemma gen_by_basis {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (h_findim : finite_dimensional K E) :
E = intermediate_field.adjoin K (finset.univ.image ((algebra_map ↥E L) ∘
finite_dimensional.fin_basis K E)) :=
begin
  apply le_antisymm,
  {
    let s : set L := (finset.image (⇑(algebra_map ↥E L) ∘ 
    ⇑(finite_dimensional.fin_basis K ↥E)) finset.univ),
    change E ≤ intermediate_field.adjoin K s,
    have h : E.to_subalgebra ≤ algebra.adjoin K s,
    {
      exact subalg_le_gen_by_basis h_findim,
    },
    have h2 : algebra.adjoin K s ≤ (intermediate_field.adjoin K s).to_subalgebra,
    {
      exact intermediate_field.algebra_adjoin_le_adjoin K s,
    },
  intros x hx,
  apply h2,
  apply h,
  exact hx,
  },
  { rw intermediate_field.adjoin_le_iff,
    intros l hl,
    simp at hl,
    rcases hl with ⟨i, rfl⟩,
    let e := (finite_dimensional.fin_basis K ↥E) i,
    exact e.2,
  },
end

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


lemma intermediate_field_map_map {K L1 L2 L3 : Type*} [field K] [field L1] [algebra K L1]
[field L2] [algebra K L2] [field L3] [algebra K L3] 
(E : intermediate_field K L1) (f : L1 →ₐ[K] L2) (g : L2 →ₐ[K] L3) : 
(E.map f).map g = E.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

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

lemma map_adjoin_le_adjoin_map {K L : Type*} [field K] [field L] [algebra K L] (S : finset L) 
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

lemma im_in_adj_roots {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} 
(h_findim : finite_dimensional K E) (σ : L ≃ₐ[K] L) : 
intermediate_field.map E σ.to_alg_hom ≤ adj_roots h_findim := 
begin
  let S := (finset.univ.image ((algebra_map ↥E L) ∘ finite_dimensional.fin_basis K E)),
  have h_gen : E = intermediate_field.adjoin K S,
  {
    exact gen_by_basis h_findim,
  },
  have h_adjoin_swap : E.map σ.to_alg_hom = intermediate_field.adjoin K (σ.to_fun '' S),
  {
    rw h_gen,
    apply le_antisymm,
    {
      exact map_adjoin_le_adjoin_map S σ,
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
    change polynomial.eval₂ (algebra_map K L) (σ.to_alg_hom a) (minpoly K a) = 0,
    rw ← polynomial.alg_hom_eval₂_algebra_map,
    have h_inj : function.injective (coe_fn σ),
    {
      exact ring_hom.injective σ.to_alg_hom.to_ring_hom,
    },
    have h_zero : σ 0 = 0,
    {
      simp, 
    },
    have h_min_kills : polynomial.eval₂ (algebra_map K L) a (minpoly K a) = 0,
    {
      exact minpoly.aeval K a,
    },
    rw h_min_kills,
    exact h_zero,
  },
  have h_root_of_prod : (polynomial.map (algebra_map K L) 
  (prod_min_polys h_findim)).is_root x,
  {
    let p := minpoly K a,
    have hp : p ∈ min_polys h_findim,
    {
      have ha' : a ∈ (finset.image (⇑(algebra_map ↥E L) ∘ 
      coe_fn(finite_dimensional.fin_basis K ↥E)) finset.univ) := ha,
      rw finset.mem_image at ha',
      cases ha' with b ha',
      cases ha' with hb ha',
      let v := (finite_dimensional.fin_basis K ↥E) b,
      have h_minpoly_eq : minpoly K v = minpoly K a,
      {
        have hva : a = v,
        {
          change (algebra_map ↥E L)((finite_dimensional.fin_basis K ↥E) b) = a
          at ha',
          rw ← ha',
          refl,
        },
        rw hva,
        refine minpoly.eq_of_algebra_map_eq (algebra_map ↥E L).injective _ rfl,
        {
          refine is_integral_of_mem_of_fg (⊤ : subalgebra K E) h_findim.out (v : E) _,
          simp,
        },
      },
      change minpoly K a ∈ min_polys h_findim,
      unfold min_polys,
      rw finset.mem_image,
      use b,
      split, 
      {
        exact finset.mem_univ b, 
      },
      {
        simp,
        exact h_minpoly_eq,
      },
    },
    exact root_prod_of_root_elem hp h_root_of_minpoly,
  },
  unfold root_finset,
  simp,
  rw polynomial.mem_roots,
  exact h_root_of_prod,
  exact polynomial.map_monic_ne_zero (prod_min_polys_monic h_findim),
end

