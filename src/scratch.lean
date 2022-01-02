import field_theory.galois 


example (A B C : Type*) [comm_ring A] [comm_ring B] [comm_ring C] 
[algebra A B] [algebra A C] (R : subalgebra A B) (f : B →ₐ[A] C) (x : R):
f x = (alg_hom.restrict_domain R f) x
:=
begin
  --unfold alg_hom.restrict_domain,
  --change f x = f ((is_scalar_tower.to_alg_hom A R B) x),
  apply congr_arg (f : B → C),
  simp,
end