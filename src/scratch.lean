import field_theory.galois
import order.filter.ultrafilter

example (X Y Z : Type*) (f : X → Y) (g : Y → Z) (s : set Z) :
f⁻¹' (g⁻¹' s) = (g ∘ f)⁻¹' s :=
begin
  refl,
end
