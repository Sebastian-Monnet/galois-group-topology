import tactic
import field_theory.galois
import data.set.basic
import algebra.group.basic
import ring_theory.tensor_product
import topology.algebra.filter_basis
import order.filter.bases 
import linear_algebra.finite_dimensional
import field_theory.intermediate_field



def normal_closure {K L : Type*} [field K] [field L] [algebra K L] (E : intermediate_field K L) : intermediate_field K L := 
Inf {N : intermediate_field K L | E ≤ N ∧ normal K N}



lemma inf_of_normal {K L : Type*} [field K] [field L] [algebra K L] (S : set (intermediate_field K L)) [S.nonempty] (H : ∀ (E : intermediate_field K L), E ∈ S → normal K E) : normal K ↥(Inf S) :=
begin 
  rw normal_iff,
  intro x,
  split, 
  {
    cases _inst_4 with E hE,
    specialize H E hE,
    have key := Inf_le hE,
    rw normal_iff at H,
    -- need to use key to view `x` as a term `y : ↥E`, and then `specialize H x`. And then somehow get from `is_integral K y` to `is_integral K x`, hopefully via some simp magic 
    sorry,
  },
  {
    unfold polynomial.splits,
  },
end 




lemma normal_closure_normal {K L : Type*} [field K] [field L] [algebra K L] [normal K L] (E : intermediate_field K L) : normal K (normal_closure E) :=
begin
   sorry,
end

lemma im_of_intermediate_field_inv_mem {K L E: Type*} [field K] [field L] [field E] [algebra K L] [algebra K E] (σ : E →ₐ[K] L) (x : L) (hx : x ∈ σ.range) : x⁻¹ ∈ σ.range :=
begin
  rcases hx with ⟨a, rfl⟩,
  use a⁻¹,
  simp,
end

def intermediate_field_range {K L E : Type*} [field E] [field K] [field L] [algebra K E] [algebra K L] (σ : E →ₐ[K] L) : intermediate_field K L := 
(alg_hom.range σ).to_intermediate_field (im_of_intermediate_field_inv_mem σ)

lemma embedding_into_normal_closure {K L : Type*} [field K] [field L] [algebra K L] (E : intermediate_field K L) (σ : ↥E →ₐ[K] L) : intermediate_field_range σ ≤ (normal_closure E) := 
 begin
   sorry 
 end

 lemma finite_dimensional_normal_closure {K L : Type*} [field K] [field L] [algebra K L] (E : intermediate_field K L) : finite_dimensional K ↥(normal_closure E) :=
 begin
   sorry, 
 end